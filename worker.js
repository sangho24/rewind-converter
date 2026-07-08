/**
 * 리와인드 컨버터 웹워커 (스펙 v1.1)
 * 인스타그램 공식 데이터 내보내기 zip(HTML 형식)을 100% 브라우저 안에서 파싱해
 * 리와인드 코드(RW1. deflate-raw base64url)를 생성한다.
 *
 * 개인정보 원칙:
 * - 어떤 데이터도 서버로 전송하지 않는다 (fetch/XHR/beacon 없음)
 * - DM 본문 텍스트는 절대 수집하지 않는다 (발신자·타임스탬프 메타만)
 * - IP·이메일·전화번호는 코드에 포함하지 않는다. 캡션은 옵트인 + @멘션 마스킹
 *
 * 타임존: 내보내기 HTML에 표기된 시각을 그대로 사용한다 (변환 없음).
 * 인스타그램 HTML 내보내기는 요청 계정의 로케일 형식으로 시각을 렌더링하며,
 * 미니앱 레퍼런스 구현과 동일한 해석을 유지한다.
 */
'use strict';

importScripts('lib/fflate.min.js');

/* ---------------- 상수 (스펙 v1.1) ---------------- */

var SIZE_LIMIT = 50 * 1024;                 // 코드 크기 강제 상한
var CAPS = {                                 // relations 배열 상한
  cleanup: 1000, oneSided: 1000, fans: 1000,
  blocked: 200, pendingSent: 100, recentRequests: 100, recentUnfollowed: 100
};
var FALLBACK_MAX_BYTES = 500 * 1024 * 1024;  // bufferZip 폴백 허용 최대 크기

/* ---------------- 공용 유틸 ---------------- */

var TD = new TextDecoder('utf-8');

var ENTITIES = { amp: '&', lt: '<', gt: '>', quot: '"', apos: "'", nbsp: ' ' };

// HTML 엔티티 해제 (워커에는 DOM이 없으므로 직접 구현)
function unesc(s) {
  if (!s || s.indexOf('&') < 0) return s;
  return s.replace(/&(#[xX]?[0-9a-fA-F]+|[a-zA-Z]+);/g, function (whole, e) {
    if (e[0] === '#') {
      var code = (e[1] === 'x' || e[1] === 'X') ? parseInt(e.slice(2), 16) : parseInt(e.slice(1), 10);
      if (isNaN(code)) return whole;
      try { return String.fromCodePoint(code); } catch (err) { return whole; }
    }
    return Object.prototype.hasOwnProperty.call(ENTITIES, e) ? ENTITIES[e] : whole;
  });
}

function stripTags(s) { return s.replace(/<[^>]+>/g, '').trim(); }

// 개행·연속 공백 정규화
function norm(s) { return s ? s.split(/\s+/).join(' ').trim() : s; }

function pad2(n) { return n < 10 ? '0' + n : '' + n; }

function inc(map, key, n) { map[key] = (map[key] || 0) + (n || 1); }

/* ---------------- 날짜 파싱 (한국어 + 영어) ---------------- */

// 한국어: "6월 23, 2026 2:06 오전"
var KDATE_KO = /(\d{1,2})월\s+(\d{1,2}),\s+(\d{4})\s+(\d{1,2}):(\d{2})\s*(오전|오후)?/;
// 영어: "Jun 23, 2026 2:06 am" / "Jun 23, 2026, 2:06 AM" / 초 포함 변형
var KDATE_EN = /\b(Jan|Feb|Mar|Apr|May|Jun|Jul|Aug|Sep|Oct|Nov|Dec)[a-z]*\.?\s+(\d{1,2}),\s+(\d{4}),?\s+(\d{1,2}):(\d{2})(?::\d{2})?(?:\s*([AaPp])\.?[Mm]?\.?)?/;
var EN_MONTH = { Jan: 1, Feb: 2, Mar: 3, Apr: 4, May: 5, Jun: 6, Jul: 7, Aug: 8, Sep: 9, Oct: 10, Nov: 11, Dec: 12 };

// 현재 변환의 언어 감지 카운터 (워커는 한 번에 한 변환만 수행)
var LANG = { ko: 0, en: 0 };

function parseKDate(s) {
  if (!s) return null;
  var m = KDATE_KO.exec(s);
  if (m) {
    LANG.ko += 1;
    var h = +m[4];
    if (m[6] === '오후' && h !== 12) h += 12;
    if (m[6] === '오전' && h === 12) h = 0;
    return m[3] + '-' + pad2(+m[1]) + '-' + pad2(+m[2]) + ' ' + pad2(h) + ':' + m[5];
  }
  m = KDATE_EN.exec(s);
  if (m) {
    LANG.en += 1;
    var he = +m[4];
    var ap = m[6] ? m[6].toLowerCase() : null;
    if (ap === 'p' && he !== 12) he += 12;
    if (ap === 'a' && he === 12) he = 0;
    return m[3] + '-' + pad2(EN_MONTH[m[1]]) + '-' + pad2(+m[2]) + ' ' + pad2(he) + ':' + m[5];
  }
  return null;
}

function day(s) { return s ? s.slice(0, 10) : ''; }

// "YYYY-MM" 최소~최대 사이 전체 월 나열
function monthRange(lo, hi) {
  var y = +lo.slice(0, 4), m = +lo.slice(5, 7);
  var out = [];
  for (;;) {
    var cur = y + '-' + pad2(m);
    out.push(cur);
    if (cur === hi) break;
    m += 1;
    if (m === 13) { y += 1; m = 1; }
    if (out.length > 1200) break; // 안전장치
  }
  return out;
}

/* ---------------- 진행 상황 보고 ---------------- */

var lastProgressAt = 0;
function progress(payload, force) {
  var now = Date.now();
  if (!force && now - lastProgressAt < 120) return;
  lastProgressAt = now;
  payload.type = 'progress';
  postMessage(payload);
}

/* ---------------- 상태 ---------------- */

function newState() {
  return {
    texts: {
      conn: {},          // 파일명(확장자 제외) -> html 텍스트
      likedPosts: null,
      likedComments: null,
      storyLikes: null,
      stories: null,
      posts: {},         // posts | posts_N | archived_posts -> html
      personal: null,
      signup: null
    },
    counts: { comments: 0, advertisers: 0, adsViewed: 0 },
    dm: {
      inbox: {},          // 폴더명 -> thread
      requests: {},
      looseInbox: {},     // 잘린 파일명 prefix -> thread (폴더 밖 루즈 HTML)
      looseRequests: {}
    },
    // 침묵 실패 방지용 도메인별 파일 수집 카운터
    health: { conn: 0, likes: 0, storyLikes: 0, stories: 0, dm: 0, posts: 0 },
    htmlSeen: 0,
    jsonSeen: 0,
    prog: { dmThreads: 0, dmMsgs: 0 }
  };
}

function newThread() {
  return { title: null, titleP: false, senders: {}, monthly: {}, total: 0 };
}

function ensureThread(st, box, folder) {
  var map = box === 'inbox' ? st.dm.inbox : st.dm.requests;
  if (!map[folder]) {
    map[folder] = newThread();
    if (box === 'inbox') st.prog.dmThreads += 1;
  }
  return map[folder];
}

/* ---------------- DM 파싱 (본문 미수집) ---------------- */

var H2_MARK = '<h2 class="_3-95 _2pim _a6-h _a6-i">';
var DATE_MARK = '<div class="_3-94 _a6-o">';
var TITLE_RE = /<title>([\s\S]*?)<\/title>/;

// 발신자 h2 → 그 다음 타임스탬프 div 순차 스캔 (레퍼런스 정규식과 동일 의미, indexOf 고속 경로)
function scanMessagesFast(text, thread) {
  var pos = 0, n = 0;
  for (;;) {
    var h = text.indexOf(H2_MARK, pos);
    if (h < 0) break;
    var he = text.indexOf('</h2>', h + H2_MARK.length);
    if (he < 0) break;
    var d = text.indexOf(DATE_MARK, he);
    if (d < 0) break;
    var de = text.indexOf('</div>', d + DATE_MARK.length);
    if (de < 0) break;
    recordMessage(thread, text.slice(h + H2_MARK.length, he), text.slice(d + DATE_MARK.length, de));
    n += 1;
    pos = de + 6;
  }
  return n;
}

// 클래스 난독화가 바뀜 내보내기용 완화 경로: 클래스 부분 일치 기반
function scanMessagesRelaxed(text, thread) {
  var re = /<h2 class="[^"]*_a6-h[^"]*">([\s\S]*?)<\/h2>|<div class="[^"]*_a6-o[^"]*">([^<]*)<\/div>/g;
  var m, sender = null, n = 0;
  while ((m = re.exec(text))) {
    if (m[1] !== undefined) {
      if (sender === null) sender = m[1];
      // 발신자 대기 중의 중간 h2는 건너뜀 (레퍼런스 lazy 매칭과 동일 의미)
    } else if (sender !== null) {
      recordMessage(thread, sender, m[2]);
      sender = null;
      n += 1;
    }
  }
  return n;
}

function recordMessage(thread, senderRaw, dateRaw) {
  var sender = stripTags(unesc(senderRaw));
  var iso = parseKDate(dateRaw);
  thread.total += 1;
  inc(thread.senders, sender);
  if (iso) inc(thread.monthly, iso.slice(0, 7));
}

function scanMessages(text, thread) {
  var n = scanMessagesFast(text, thread);
  if (n === 0 && text.indexOf('<h2 ') >= 0) n = scanMessagesRelaxed(text, thread);
  return n;
}

function applyTitle(thread, text, isFirstFile) {
  if (thread.titleP) return;
  var tm = TITLE_RE.exec(text);
  if (tm) {
    var t = norm(stripTags(unesc(tm[1])));
    if (t && (thread.title === null || isFirstFile)) thread.title = t;
    if (isFirstFile) thread.titleP = true;
  }
}

/* ---------------- zip 엔트리 라우팅 ---------------- */

var RE_CONN = /(?:^|\/)connections\/followers_and_following\/([^\/]+)\.html$/;
var RE_LIKES = /(?:^|\/)your_instagram_activity\/likes\/(liked_posts|liked_comments)\.html$/;
var RE_STORY_LIKES = /(?:^|\/)your_instagram_activity\/story_interactions\/story_likes\.html$/;
var RE_MEDIA = /(?:^|\/)your_instagram_activity\/media\/(stories|posts|posts_\d+|archived_posts)\.html$/;
var RE_PERSONAL = /(?:^|\/)personal_information\/personal_information\/(personal_information|instagram_profile_information)\.html$/;
var RE_SIGNUP = /(?:^|\/)security_and_login_information\/login_and_profile_creation\/signup_details\.html$/;
var RE_COMMENTS = /(?:^|\/)your_instagram_activity\/comments\/(post_comments_\d+|reels_comments)\.html$/;
var RE_ADVERTISERS = /(?:^|\/)ads_information\/instagram_ads_and_businesses\/advertisers_using_your_activity_or_information\.html$/;
var RE_ADS_VIEWED = /(?:^|\/)ads_information\/ads_and_topics\/ads_viewed\.html$/;
var RE_MSG_DIR = /(?:^|\/)your_instagram_activity\/messages\/(inbox|message_requests)\/([^\/]+)\//;
var RE_MSG_FILE = /(?:^|\/)your_instagram_activity\/messages\/(inbox|message_requests)\/([^\/]+)\/(message_\d+)\.html$/;
var RE_MSG_LOOSE = /(?:^|\/)your_instagram_activity\/messages\/(inbox|message_requests)\/([^\/]+)\.html$/;
var RE_JSON_EXPORT = /(?:^|\/)(?:connections\/followers_and_following|your_instagram_activity\/(?:likes|messages|media|story_interactions))\/.*\.json$/;

// 스레드 폴더 등록 (메시지 HTML이 없어도 폴더는 대화 수에 포함)
function noteDirs(name, st) {
  var m = RE_MSG_DIR.exec(name);
  if (m) ensureThread(st, m[1], m[2]);
  if (RE_JSON_EXPORT.test(name)) st.jsonSeen += 1;
}

// 해제(start)할 가치가 있는 엔트리인지 판단해 라우트 반환
function routeOf(name) {
  var m;
  if ((m = RE_MSG_FILE.exec(name))) return { t: 'dm', box: m[1], folder: m[2], file: m[3] };
  if ((m = RE_MSG_LOOSE.exec(name))) return { t: 'dmLoose', box: m[1], base: m[2] };
  if ((m = RE_CONN.exec(name))) return { t: 'conn', key: m[1] };
  if ((m = RE_LIKES.exec(name))) return { t: m[1] === 'liked_posts' ? 'likedPosts' : 'likedComments' };
  if (RE_STORY_LIKES.test(name)) return { t: 'storyLikes' };
  if ((m = RE_MEDIA.exec(name))) return m[1] === 'stories' ? { t: 'stories' } : { t: 'posts', key: m[1] };
  if ((m = RE_PERSONAL.exec(name))) return { t: 'personal', key: m[1] };
  if (RE_SIGNUP.test(name)) return { t: 'signup' };
  if (RE_COMMENTS.test(name)) return { t: 'comments' };
  if (RE_ADVERTISERS.test(name)) return { t: 'advertisers' };
  if (RE_ADS_VIEWED.test(name)) return { t: 'adsViewed' };
  return null;
}

function countMatches(text, re) {
  var n = 0;
  re.lastIndex = 0;
  while (re.exec(text)) n += 1;
  return n;
}

function handleFile(route, text, st) {
  st.htmlSeen += 1;
  switch (route.t) {
    case 'dm': {
      st.health.dm += 1;
      var th = ensureThread(st, route.box, route.folder);
      applyTitle(th, text, route.file === 'message_1');
      var n = scanMessages(text, th);
      if (route.box === 'inbox') st.prog.dmMsgs += n;
      break;
    }
    case 'dmLoose': {
      st.health.dm += 1;
      var prefix = route.base.replace(/_+$/, '');
      var map = route.box === 'inbox' ? st.dm.looseInbox : st.dm.looseRequests;
      var lt = map[prefix] || (map[prefix] = newThread());
      applyTitle(lt, text, true);
      var ln = scanMessages(text, lt);
      if (route.box === 'inbox') st.prog.dmMsgs += ln;
      break;
    }
    case 'conn': st.health.conn += 1; st.texts.conn[route.key] = text; break;
    case 'likedPosts': st.health.likes += 1; st.texts.likedPosts = text; break;
    case 'likedComments': st.health.likes += 1; st.texts.likedComments = text; break;
    case 'storyLikes': st.health.storyLikes += 1; st.texts.storyLikes = text; break;
    case 'stories': st.health.stories += 1; st.texts.stories = text; break;
    case 'posts': st.health.posts += 1; st.texts.posts[route.key] = text; break;
    case 'personal':
      // personal_information.html 우선, 없으면 instagram_profile_information.html
      if (route.key === 'personal_information' || !st.texts.personal) st.texts.personal = text;
      break;
    case 'signup': st.texts.signup = text; break;
    case 'comments': st.counts.comments += countMatches(text, />(?:Time|시간)<\/td>/g); break;
    case 'advertisers': st.counts.advertisers = countMatches(text, /<div class="_a6-p">[^<]+<\/div>/g); break;
    case 'adsViewed': st.counts.adsViewed = countMatches(text, /<div class="_3-95 _a6-p">/g); break;
  }
}

/* ---------------- zip 스트리밍 해제 ---------------- */

function streamZip(file, st, baseBytes, totalBytes) {
  return new Promise(function (resolve, reject) {
    var uz = new fflate.Unzip();
    uz.register(fflate.UnzipInflate);
    var pending = 0, streamDone = false, failed = false;

    function fail(err) {
      if (failed) return;
      failed = true;
      reject(err instanceof Error ? err : new Error(String(err)));
    }
    function maybeDone() {
      if (streamDone && pending === 0 && !failed) resolve();
    }

    uz.onfile = function (f) {
      var name = f.name.replace(/\\/g, '/');
      noteDirs(name, st);
      var route = routeOf(name);
      if (!route) return; // 미디어 등 불필요 파일은 해제하지 않고 통과
      pending += 1;
      var parts = [], plen = 0;
      f.ondata = function (err, dat, final) {
        if (failed) return;
        if (err) { fail(err); return; }
        if (dat && dat.length) { parts.push(dat); plen += dat.length; }
        if (final) {
          var buf;
          if (parts.length === 1) buf = parts[0];
          else {
            buf = new Uint8Array(plen);
            var o = 0;
            for (var i = 0; i < parts.length; i++) { buf.set(parts[i], o); o += parts[i].length; }
          }
          try { handleFile(route, TD.decode(buf), st); }
          catch (e) { /* 개별 파일 파싱 실패는 건너뛴다 (관대 규칙) */ }
          parts = null;
          pending -= 1;
          maybeDone();
        }
      };
      try { f.start(); } catch (e) { pending -= 1; }
    };

    var reader = file.stream().getReader();
    var read = 0;
    function pump() {
      reader.read().then(function (r) {
        if (failed) return;
        if (r.done) {
          try { uz.push(new Uint8Array(0), true); } catch (e) { fail(e); return; }
          streamDone = true;
          maybeDone();
          return;
        }
        read += r.value.length;
        try { uz.push(r.value); } catch (e) { fail(e); return; }
        progress({ stage: 'unzip', bytes: baseBytes + read, total: totalBytes, dmThreads: st.prog.dmThreads, dmMsgs: st.prog.dmMsgs });
        pump();
      }, fail);
    }
    pump();
  });
}

// 스트리밍 실패 시 폴백: 전체 버퍼 unzip (필요 파일만 필터) — 대형 파일은 명시적 에러
function bufferZip(file, st) {
  if (file.size > FALLBACK_MAX_BYTES) {
    return Promise.reject(Object.assign(
      new Error('zip 스트리밍 해제에 실패했고, 파일이 커서(500MB 초과) 대체 방식을 쓸 수 없어요. 최신 Chrome/Edge에서 다시 시도해 주세요.'),
      { kind: 'too-big-fallback' }
    ));
  }
  return file.arrayBuffer().then(function (ab) {
    return new Promise(function (resolve, reject) {
      fflate.unzip(new Uint8Array(ab), {
        filter: function (f) {
          var name = f.name.replace(/\\/g, '/');
          noteDirs(name, st);
          return !!routeOf(name);
        }
      }, function (err, files) {
        if (err) { reject(err); return; }
        try {
          var names = Object.keys(files);
          for (var i = 0; i < names.length; i++) {
            var name = names[i].replace(/\\/g, '/');
            var route = routeOf(name);
            if (route) {
              try { handleFile(route, TD.decode(files[names[i]]), st); } catch (e) { /* skip */ }
            }
          }
          resolve();
        } catch (e) { reject(e); }
      });
    });
  });
}

/* ---------------- 팔로우 관계 파싱 ---------------- */

// 링크형: <a target="_blank" href="https://www.instagram.com/USER">TEXT</a></div><div>DATE</div>
// 테이블형: [<td>이름|Name</td><td>NAME</td>] <td>사용자 이름|Username</td><td>USER</td></table> ... 날짜 div
function parseConnFile(text) {
  if (!text) return [];
  var seen = {}, order = [], names = {};
  var m;
  var re1 = /<a\s+target="_blank"\s+href="https:\/\/www\.instagram\.com\/([^"]+)">([^<]*)<\/a>\s*<\/div>\s*(?:<div>([^<]*)<\/div>)?/g;
  while ((m = re1.exec(text))) {
    var u = m[1].trim().replace(/^\/+|\/+$/g, '').split('?')[0];
    if (u.indexOf('_u/') === 0) u = u.slice(3);
    if (!u) u = m[2].trim();
    if (u && !Object.prototype.hasOwnProperty.call(seen, u)) {
      seen[u] = parseKDate(m[3] || '');
      order.push(u);
    }
  }
  var re2 = /(?:<td class="[^"]*">(?:이름|Name)<\/td><td class="[^"]*">([^<]+)<\/td><\/tr><tr>)?<td class="[^"]*">(?:사용자 이름|Username)<\/td><td class="[^"]*">([^<]+)<\/td><\/tr><\/table>[\s\S]*?<div class="[^"]*_a6-o[^"]*">([^<]*)<\/div>/g;
  while ((m = re2.exec(text))) {
    var u2 = unesc(m[2]).trim();
    if (u2 && !Object.prototype.hasOwnProperty.call(seen, u2)) {
      seen[u2] = parseKDate(m[3] || '');
      order.push(u2);
      if (m[1] && m[1].trim()) names[u2] = norm(unesc(m[1]));
    }
  }
  return order.map(function (u) {
    var e = { u: u, d: seen[u] };
    if (names[u]) e.name = names[u];
    return e;
  });
}

function buildConnections(st) {
  var conn = st.texts.conn;
  var followers = [];
  Object.keys(conn).sort().forEach(function (key) {
    if (/^followers(_\d+)?$/.test(key)) followers = followers.concat(parseConnFile(conn[key]));
  });
  var out = {
    followers: followers,
    following: parseConnFile(conn['following']),
    closeFriends: parseConnFile(conn['close_friends']),
    blocked: parseConnFile(conn['blocked_profiles']),
    pendingSent: parseConnFile(conn['pending_follow_requests']),
    recentRequests: parseConnFile(conn['recent_follow_requests']),
    recentUnfollowed: parseConnFile(conn['recently_unfollowed_profiles'])
  };
  var items = 0, dated = 0;
  Object.keys(out).forEach(function (k) {
    out[k].forEach(function (e) { items += 1; if (e.d) dated += 1; });
  });
  out.stats = { items: items, dated: dated };
  return out;
}

/* ---------------- 좋아요 파싱 ---------------- */

var DATE_DIV_RE_SRC = '<div class="[^"]*_a6-o[^"]*">([^<]*)<\\/div>';

function buildLikes(st) {
  var perUser = {}, monthly = {};
  var total = 0, dated = 0;
  var m;
  if (st.texts.likedPosts) {
    // 테이블형(중첩): 날짜 div 사이 구간에서 마지막 '사용자 이름/Username' 값 사용
    var text = st.texts.likedPosts;
    var dre = new RegExp(DATE_DIV_RE_SRC, 'g');
    var prev = 0;
    while ((m = dre.exec(text))) {
      var chunk = text.slice(prev, m.index);
      prev = dre.lastIndex;
      var ure = /(?:사용자 이름|Username)<\/td><td[^>]*>([^<]*)<\/td>/g;
      var um, last = null;
      while ((um = ure.exec(chunk))) last = um[1];
      var u = last ? unesc(last).trim() : null;
      var iso = parseKDate(m[1]);
      total += 1;
      if (u) inc(perUser, u);
      if (iso) { dated += 1; inc(monthly, iso.slice(0, 7)); }
    }
  }
  if (st.texts.likedComments) {
    // 링크형 변형: <h2>USER</h2> ... <a href=URL>...</a></div><div>DATE</div>
    var cre = /<h2 class="[^"]*_a6-h[^"]*">([^<]*)<\/h2><div class="[^"]*_a6-p[^"]*"><div><div><a target="_blank" href="https:\/\/www\.instagram\.com\/[^"]*">[^<]*<\/a><\/div><div>([^<]*)<\/div>/g;
    while ((m = cre.exec(st.texts.likedComments))) {
      var u2 = unesc(m[1]).trim();
      var iso2 = parseKDate(m[2]);
      total += 1;
      if (u2) inc(perUser, u2);
      if (iso2) { dated += 1; inc(monthly, iso2.slice(0, 7)); }
    }
  }
  return {
    total: total, dated: dated,
    perUser: perUser, monthly: monthly,
    unique: Object.keys(perUser).length
  };
}

/* ---------------- 스토리 좋아요 파싱 ---------------- */

function parseStoryLikeChunk(ch, perUser, monthly) {
  var dm, lastDate = null;
  var dre = new RegExp(DATE_DIV_RE_SRC, 'g');
  while ((dm = dre.exec(ch))) lastDate = dm[1];
  var iso = lastDate ? parseKDate(lastDate) : null;
  var um = /(?:사용자 이름|Username)<\/td><td[^>]*>([^<]+)<\/td>/.exec(ch);
  var u = um ? unesc(um[1]).trim() : null;
  if (!u) {
    var sm = /instagram\.com\/stories\/([^\/"]+)\//.exec(ch);
    if (sm) u = sm[1];
  }
  if (u) inc(perUser, u);
  if (iso) inc(monthly, iso.slice(0, 7));
  return !!iso;
}

function buildStoryLikes(st) {
  var perUser = {}, monthly = {}, total = 0, dated = 0;
  var text = st.texts.storyLikes;
  if (text) {
    var mainIdx = text.indexOf('<main');
    var body = mainIdx >= 0 ? text.slice(mainIdx) : text;
    var chunks = body.split('<div class="_3-95 _a6-p">').slice(1);
    if (chunks.length === 0) {
      // 클래스 드리프트 폴백: 날짜 div 기준 청킹
      var dre = new RegExp(DATE_DIV_RE_SRC, 'g');
      var m, prev = 0;
      while ((m = dre.exec(body))) {
        var chunk = body.slice(prev, dre.lastIndex);
        prev = dre.lastIndex;
        total += 1;
        if (parseStoryLikeChunk(chunk, perUser, monthly)) dated += 1;
      }
    } else {
      for (var i = 0; i < chunks.length; i++) {
        total += 1;
        if (parseStoryLikeChunk(chunks[i], perUser, monthly)) dated += 1;
      }
    }
  }
  return { total: total, dated: dated, perUser: perUser, monthly: monthly };
}

/* ---------------- 내 스토리(stories.html) 파싱 ---------------- */

var STORY_ITEM_MARK = '<div class="pam _3-95 _2ph- _a6-g uiBoxWhite noborder">';
var STORY_ITEM_RELAX = /<div class="pam [^"]*uiBoxWhite[^"]*">/;
var STORY_CAPTION_RE = /^<h2 class="[^"]*">([\s\S]*?)<\/h2>/;

function buildStories(st) {
  var items = [];
  var splitCount = 0;
  var text = st.texts.stories;
  if (text) {
    var chunks = text.split(STORY_ITEM_MARK).slice(1);
    if (chunks.length === 0) {
      // 클래스 드리프트 폴백: 완화 정규식으로 분할
      chunks = text.split(new RegExp(STORY_ITEM_RELAX.source)).slice(1);
    }
    splitCount = chunks.length;
    for (var i = 0; i < chunks.length; i++) {
      var ch = chunks[i];
      var cm = STORY_CAPTION_RE.exec(ch);
      var caption = cm ? unesc(cm[1]).trim() : '';
      var dm, iso = null;
      var dre = new RegExp(DATE_DIV_RE_SRC, 'g');
      while ((dm = dre.exec(ch))) {
        var t = parseKDate(dm[1]);
        if (t) iso = t; // 항목 마지막 타임스탬프 사용
      }
      if (!iso) continue;
      items.push({ date: iso, caption: caption });
    }
    items.sort(function (a, b) { return a.date < b.date ? -1 : a.date > b.date ? 1 : 0; });
  }
  var byYear = {}, monthly = {};
  for (var j = 0; j < items.length; j++) {
    inc(byYear, items[j].date.slice(0, 4));
    inc(monthly, items[j].date.slice(0, 7));
  }
  return { items: items, byYear: byYear, monthly: monthly, total: items.length, splitCount: splitCount };
}

/* ---------------- 게시물/콘텐츠 통계 ---------------- */

function countPostItems(text) {
  if (!text) return { count: 0, lastDate: null };
  var mainIdx = text.search(/<main[^>]*>/);
  var body = mainIdx >= 0 ? text.slice(mainIdx) : text;
  var re = new RegExp(DATE_DIV_RE_SRC, 'g');
  var m, count = 0, lastDate = null;
  while ((m = re.exec(body))) {
    count += 1;
    var iso = parseKDate(m[1]);
    if (iso && (!lastDate || iso > lastDate)) lastDate = iso;
  }
  return { count: count, lastDate: lastDate };
}

function buildContent(st, storiesTotal) {
  var posts = st.texts.posts;
  var keys = Object.keys(posts);
  if (!keys.length && !storiesTotal) return null;
  var active = 0, totalMain = null, archived = 0, lastDate = null;
  keys.forEach(function (k) {
    var r = countPostItems(posts[k]);
    if (r.lastDate && (!lastDate || r.lastDate > lastDate)) lastDate = r.lastDate;
    if (k === 'posts') totalMain = r.count;
    else if (k === 'archived_posts') archived = r.count;
    else active += r.count;
  });
  var total = totalMain !== null ? totalMain : active + archived;
  return {
    posts: total,
    activePosts: active,
    archivedPosts: archived,
    stories: storiesTotal,
    lastPost: lastDate ? day(lastDate) : null
  };
}

/* ---------------- DM 집계 ---------------- */

function mergeThread(into, from) {
  if (!into.title && from.title) into.title = from.title;
  Object.keys(from.senders).forEach(function (s) { inc(into.senders, s, from.senders[s]); });
  Object.keys(from.monthly).forEach(function (mo) { inc(into.monthly, mo, from.monthly[mo]); });
  into.total += from.total;
}

// 폴더명 잘림으로 루트에 놓인 루즈 HTML을 대응 폴더(메시지 0건)에 병합
function mergeLoose(threads, loose) {
  var folders = Object.keys(threads);
  Object.keys(loose).forEach(function (prefix) {
    var target = null;
    for (var i = 0; i < folders.length; i++) {
      if (folders[i].indexOf(prefix) === 0 && threads[folders[i]].total === 0) { target = folders[i]; break; }
    }
    if (!target) {
      for (var j = 0; j < folders.length; j++) {
        if (folders[j].indexOf(prefix) === 0) { target = folders[j]; break; }
      }
    }
    if (target) mergeThread(threads[target], loose[prefix]);
    else threads[prefix] = loose[prefix];
  });
}

function usernameGuess(folder) {
  var m = /^(.*)_(\d{10,})$/.exec(folder);
  return m && m[1] ? m[1] : null;
}

// DM 소유자(본인) 판정 — 프로필 대조 1순위, 등장 빈도 휴리스틱 폴백 (스펙 v1.1)
function pickOwner(threads, profile) {
  var appear = {}, appearOrder = [];
  threads.forEach(function (t) {
    Object.keys(t.senders).forEach(function (s) {
      if (!(s in appear)) appearOrder.push(s);
      inc(appear, s);
    });
  });
  if (profile.displayName && appear[profile.displayName]) {
    return { owner: profile.displayName, confidence: 'high' };
  }
  if (profile.username && appear[profile.username]) {
    return { owner: profile.username, confidence: 'high' };
  }
  var owner = null, best = -1;
  appearOrder.forEach(function (s) {
    if (appear[s] > best) { best = appear[s]; owner = s; }
  });
  return { owner: owner, confidence: 'low' };
}

function buildDm(st, profile) {
  mergeLoose(st.dm.inbox, st.dm.looseInbox);
  mergeLoose(st.dm.requests, st.dm.looseRequests);

  var inboxKeys = Object.keys(st.dm.inbox);
  var reqKeys = Object.keys(st.dm.requests);
  var threads = inboxKeys.map(function (k) {
    var t = st.dm.inbox[k];
    return { folder: k, title: t.title, senders: t.senders, monthly: t.monthly, total: t.total };
  });

  var ownerPick = pickOwner(threads, profile);
  var owner = ownerPick.owner;

  var totalInbox = 0, sent = 0, datedInbox = 0;
  var monthlyInbox = {};
  threads.forEach(function (t) {
    totalInbox += t.total;
    sent += t.senders[owner] || 0;
    Object.keys(t.monthly).forEach(function (mo) {
      inc(monthlyInbox, mo, t.monthly[mo]);
      datedInbox += t.monthly[mo];
    });
  });

  var reqMessages = 0, datedReq = 0;
  var monthlyAll = {};
  Object.keys(monthlyInbox).forEach(function (mo) { monthlyAll[mo] = monthlyInbox[mo]; });
  reqKeys.forEach(function (k) {
    var t = st.dm.requests[k];
    reqMessages += t.total;
    Object.keys(t.monthly).forEach(function (mo) {
      inc(monthlyAll, mo, t.monthly[mo]);
      datedReq += t.monthly[mo];
    });
  });

  // 상위 10 대화
  var sorted = threads.slice().sort(function (a, b) { return b.total - a.total; });
  var top = sorted.slice(0, 10).map(function (t) {
    var mine = t.senders[owner] || 0;
    return {
      name: norm(t.title) || usernameGuess(t.folder) || t.folder,
      n: t.total,
      ratio: t.total ? Math.round((mine / t.total) * 1000) / 1000 : 0
    };
  });

  return {
    owner: owner,
    ownerConfidence: ownerPick.confidence,
    threads: threads,
    conversations: inboxKeys.length,
    totalInbox: totalInbox,
    sent: sent,
    received: totalInbox - sent,
    reqThreads: reqKeys.length,
    reqMessages: reqMessages,
    monthlyInbox: monthlyInbox,
    monthlyAll: monthlyAll,
    top: top,
    stats: { items: totalInbox + reqMessages, dated: datedInbox + datedReq }
  };
}

/* ---------------- 피크·공백기 ---------------- */

function topMonths(monthly, k) {
  return Object.keys(monthly)
    .sort(function (a, b) { return monthly[b] - monthly[a] || (a < b ? -1 : 1); })
    .slice(0, k);
}

function buildStoryPeaks(stories) {
  var months = topMonths(stories.monthly, 5).sort();
  var peaks = months.map(function (mo) {
    var seen = {}, captions = [];
    for (var i = 0; i < stories.items.length; i++) {
      var s = stories.items[i];
      if (s.date.slice(0, 7) !== mo) continue;
      var c = norm(s.caption);
      if (!c || seen[c]) continue;
      seen[c] = true;
      captions.push(c);
      if (captions.length >= 15) break;
    }
    return { month: mo, count: stories.monthly[mo], captions: captions };
  });
  peaks.sort(function (a, b) { return b.count - a.count; });
  return peaks;
}

function buildDmPeaks(dm) {
  var months = topMonths(dm.monthlyInbox, 5);
  var peaks = months.map(function (mo) {
    var partners = dm.threads
      .map(function (t) { return { name: norm(t.title) || usernameGuess(t.folder) || t.folder, n: t.monthly[mo] || 0 }; })
      .sort(function (a, b) { return b.n - a.n; })
      .slice(0, 3)
      .filter(function (p) { return p.n > 0; });
    return { month: mo, count: dm.monthlyInbox[mo], top: partners };
  });
  peaks.sort(function (a, b) { return b.count - a.count; });
  return peaks;
}

// 공백기 (스펙 v1.1): 본인 활동 월 중앙값의 20% 미만이 2개월 이상 지속.
// 총 DM 1,000건 미만 계정은 미생성. 절대값 임계 금지.
function buildDroughts(monthly, totalInbox) {
  if (!totalInbox || totalInbox < 1000) return [];
  var keys = Object.keys(monthly).sort();
  if (!keys.length) return [];
  var months = monthRange(keys[0], keys[keys.length - 1]);
  var active = months.map(function (mo) { return monthly[mo] || 0; })
    .filter(function (v) { return v > 0; })
    .sort(function (a, b) { return a - b; });
  if (!active.length) return [];
  var mid = Math.floor(active.length / 2);
  var median = active.length % 2 ? active[mid] : (active[mid - 1] + active[mid]) / 2;
  var threshold = median * 0.2;
  if (threshold <= 0) return [];

  var runs = [], cur = [];
  months.forEach(function (mo) {
    if ((monthly[mo] || 0) < threshold) cur.push(mo);
    else { if (cur.length) runs.push(cur); cur = []; }
  });
  if (cur.length) runs.push(cur);
  runs = runs.filter(function (r) {
    return r.length >= 2 && r[0] !== months[0]; // 2개월 이상 + 계정 초기 구간 제외
  });
  var sum = function (r) { return r.reduce(function (a, mo) { return a + (monthly[mo] || 0); }, 0); };
  runs.sort(function (a, b) { return b.length - a.length || sum(a) - sum(b); });
  return runs.slice(0, 2).map(function (r) {
    var i0 = months.indexOf(r[0]), i1 = months.indexOf(r[r.length - 1]);
    return {
      from: r[0],
      to: r[r.length - 1],
      months: r.length,
      dmCount: sum(r),
      before: i0 > 0 ? (monthly[months[i0 - 1]] || 0) : null,
      after: i1 + 1 < months.length ? (monthly[months[i1 + 1]] || 0) : null
    };
  });
}

/* ---------------- 교차 분석 (참여도 = 게시물 좋아요 + 스토리 좋아요) ---------------- */

function buildCross(conn, likes, storyLikes) {
  var engagement = {};
  Object.keys(likes.perUser).forEach(function (u) { inc(engagement, u, likes.perUser[u]); });
  Object.keys(storyLikes.perUser).forEach(function (u) { inc(engagement, u, storyLikes.perUser[u]); });

  var followersMap = {}, followingMap = {};
  conn.followers.forEach(function (e) { if (!(e.u in followersMap)) followersMap[e.u] = e.d; });
  conn.following.forEach(function (e) { if (!(e.u in followingMap)) followingMap[e.u] = e.d; });

  var mutual = [], nfb = [], fans = [];
  Object.keys(followingMap).forEach(function (u) {
    if (u in followersMap) mutual.push(u);
    else nfb.push({ u: u, d: followingMap[u] });
  });
  Object.keys(followersMap).forEach(function (u) {
    if (!(u in followingMap)) fans.push({ u: u, d: followersMap[u] });
  });

  var cleanup = nfb
    .filter(function (e) { return (engagement[e.u] || 0) === 0; })
    .sort(function (a, b) { return (a.d || '') < (b.d || '') ? -1 : (a.d || '') > (b.d || '') ? 1 : 0; })
    .map(function (e) { return { u: e.u, d: day(e.d) }; });

  var oneSided = nfb
    .filter(function (e) { return (engagement[e.u] || 0) > 0; })
    .sort(function (a, b) { return (engagement[b.u] || 0) - (engagement[a.u] || 0); })
    .map(function (e) { return { u: e.u, d: day(e.d), e: engagement[e.u] }; });

  fans.sort(function (a, b) { return (b.d || '') < (a.d || '') ? -1 : (b.d || '') > (a.d || '') ? 1 : 0; });

  var cfSet = {};
  conn.closeFriends.forEach(function (e) { cfSet[e.u] = true; });

  var besties = mutual
    .filter(function (u) { return (engagement[u] || 0) > 0; })
    .sort(function (a, b) { return (engagement[b] || 0) - (engagement[a] || 0); })
    .slice(0, 15)
    .map(function (u) { return { u: u, e: engagement[u], cf: !!cfSet[u] }; });

  return {
    followers: Object.keys(followersMap).length,
    following: Object.keys(followingMap).length,
    mutual: mutual.length,
    cleanup: cleanup,
    oneSided: oneSided,
    fans: fans.map(function (e) { return { u: e.u, d: day(e.d) }; }),
    besties: besties
  };
}

/* ---------------- 프로필 (username / 이름 / 가입일) ---------------- */

function buildProfile(st) {
  var username = null, displayName = null, signupDate = null;
  if (st.texts.personal) {
    var um = /(?:사용자 이름|Username)<div><div>([^<]*)<\/div>/.exec(st.texts.personal);
    if (um && um[1].trim()) username = unesc(um[1]).trim();
    var nm = />(?:이름|Name)<div><div>([^<]*)<\/div>/.exec(st.texts.personal);
    if (nm && nm[1].trim()) displayName = norm(unesc(nm[1]));
  }
  if (st.texts.signup) {
    var sm = /(?:시간|Time)<\/td><td[^>]*>([^<]+)<\/td>/.exec(st.texts.signup);
    if (sm) {
      var iso = parseKDate(sm[1]);
      if (iso) signupDate = day(iso);
    }
  }
  return { username: username, displayName: displayName, signupDate: signupDate };
}

/* ---------------- 무결성 점검 (침묵 실패 금지, 스펙 v1.1) ---------------- */

function detectLang(st) {
  if (LANG.ko > LANG.en) return 'ko';
  if (LANG.en > 0) return 'en';
  // 날짜 파싱이 전무하면 라벨로 추정
  var t = st.texts.personal || st.texts.conn['following'] || '';
  if (t.indexOf('사용자 이름') >= 0) return 'ko';
  if (t.indexOf('Username') >= 0) return 'en';
  return 'other';
}

function buildHealth(st, connStats, likes, storyLikes, stories, dm) {
  var warnings = [];
  function check(label, files, items, dated) {
    if (!files) return;
    if (items === 0) { warnings.push(label + ': 파일은 있지만 항목을 찾지 못했어요'); return; }
    if (dated === 0) { warnings.push(label + ': 날짜를 하나도 해석하지 못했어요'); return; }
    if (dated / items < 0.5) warnings.push(label + ': 날짜 해석률이 ' + Math.round((dated / items) * 100) + '%에 그쳤어요');
  }
  check('팔로우 관계', st.health.conn, connStats.items, connStats.dated);
  check('좋아요', st.health.likes, likes.total, likes.dated);
  check('스토리 좋아요', st.health.storyLikes, storyLikes.total, storyLikes.dated);
  check('내 스토리', st.health.stories, stories.splitCount, stories.total);
  check('DM', st.health.dm, dm.stats.items, dm.stats.dated);
  return { ok: warnings.length === 0, warnings: warnings };
}

/* ---------------- 조립 ---------------- */

function assemble(st, conn, likes, storyLikes, stories, dm, profile, lang) {
  var cross = buildCross(conn, likes, storyLikes);

  // 공통 월 축: 세 시리즈의 최소~최대 월 (데이터 파생, 하드코딩 금지)
  var monthKeys = Object.keys(likes.monthly)
    .concat(Object.keys(storyLikes.monthly))
    .concat(Object.keys(dm.monthlyAll))
    .sort();
  var months = monthKeys.length ? monthRange(monthKeys[0], monthKeys[monthKeys.length - 1]) : [];
  var fill = function (m) { return months.map(function (mo) { return m[mo] || 0; }); };

  var today = new Date();
  var generatedAt = today.getFullYear() + '-' + pad2(today.getMonth() + 1) + '-' + pad2(today.getDate());

  return {
    v: 1,
    generatedAt: generatedAt,
    displayName: profile.displayName,
    username: profile.username,
    signupDate: profile.signupDate,
    truncated: false,
    lang: lang,

    hero: {
      followers: cross.followers,
      following: cross.following,
      mutual: cross.mutual,
      dmTotal: dm.totalInbox
    },

    relations: {
      totals: {
        cleanup: cross.cleanup.length,
        oneSided: cross.oneSided.length,
        fans: cross.fans.length
      },
      cleanup: cross.cleanup.slice(0, CAPS.cleanup),
      oneSided: cross.oneSided.slice(0, CAPS.oneSided),
      fans: cross.fans.slice(0, CAPS.fans),
      blocked: conn.blocked.slice(0, CAPS.blocked).map(function (e) { return { u: e.u, n: e.name || null }; }),
      pendingSent: conn.pendingSent.slice(0, CAPS.pendingSent).map(function (e) { return { u: e.u, d: day(e.d) }; }),
      recentRequests: conn.recentRequests.slice(0, CAPS.recentRequests).map(function (e) { return { u: e.u, d: day(e.d) }; }),
      recentUnfollowed: conn.recentUnfollowed.slice(0, CAPS.recentUnfollowed).map(function (e) { return { u: e.u, d: day(e.d) }; }),
      closeFriendsCount: conn.closeFriends.length
    },

    besties: cross.besties,

    months: months,
    series: {
      likes: fill(likes.monthly),
      storyLikes: fill(storyLikes.monthly),
      dm: fill(dm.monthlyAll)
    },

    storiesByYear: stories.byYear,
    likesTotal: likes.total,
    likesUniqueAccounts: likes.unique,
    storyLikesTotal: storyLikes.total,
    commentsTotal: st.counts.comments,

    dm: {
      conversations: dm.conversations,
      sent: dm.sent,
      received: dm.received,
      reqThreads: dm.reqThreads,
      reqMessages: dm.reqMessages,
      ownerConfidence: dm.ownerConfidence,
      top: dm.top
    },

    content: buildContent(st, stories.total),

    peaks: {
      story: buildStoryPeaks(stories),
      dm: buildDmPeaks(dm),
      droughts: buildDroughts(dm.monthlyInbox, dm.totalInbox)
    },

    extras: {
      adsAdvertisers: st.counts.advertisers || null,
      adsViewedWeek: st.counts.adsViewed || null,
      insights: null,
      chronicle: null
    }
  };
}

/* ---------------- 캡션 위생 처리 (스펙 v1.1) ---------------- */

// 이메일·전화번호 무조건 제거, @멘션 마스킹
function sanitizeCaption(c) {
  var s = c;
  s = s.replace(/[\w.+-]+@[\w-]+(?:\.[\w-]+)+/g, '');  // 이메일 제거
  s = s.replace(/\+?\d[\d\s().-]{6,}\d/g, '');          // 전화번호 패턴 제거
  s = s.replace(/@[A-Za-z0-9._]+/g, '@***');            // 멘션 마스킹
  return norm(s) || '';
}

/* ---------------- 인코딩 (RW1. deflate-raw base64url + 크기 강제) ---------------- */

function b64url(u8) {
  var s = '';
  var CH = 0x8000;
  for (var i = 0; i < u8.length; i += CH) {
    s += String.fromCharCode.apply(null, u8.subarray(i, Math.min(i + CH, u8.length)));
  }
  return btoa(s).replace(/\+/g, '-').replace(/\//g, '_').replace(/=+$/, '');
}

function encodeRewind(data) {
  var json = JSON.stringify(data);
  var u8 = new TextEncoder().encode(json);
  // 1순위: 브라우저 표준 CompressionStream
  if (typeof CompressionStream === 'function') {
    try {
      var cs = new CompressionStream('deflate-raw');
      var stream = new Blob([u8]).stream().pipeThrough(cs);
      return new Response(stream).arrayBuffer().then(function (buf) {
        return 'RW1.' + b64url(new Uint8Array(buf));
      }).catch(function () {
        return fallbackEncode(u8);
      });
    } catch (e) { /* deflate-raw 미지원 → 폴백 */ }
  }
  return Promise.resolve(fallbackEncode(u8));
}

function fallbackEncode(u8) {
  // 2순위: fflate raw deflate (RW1과 바이트 호환), 3순위: 무압축 RW1P
  try { return 'RW1.' + b64url(fflate.deflateSync(u8, { level: 9 })); }
  catch (e) { return 'RW1P.' + b64url(u8); }
}

// 상한 절반 적용 (절단 1단계): 정렬 우선순위(참여 높은 순/날짜 오래된 순)는 배열 앞쪽 유지
function halveRelations(rel) {
  Object.keys(CAPS).forEach(function (k) {
    if (Array.isArray(rel[k])) rel[k] = rel[k].slice(0, Math.floor(CAPS[k] / 2));
  });
}

// 캡션 옵트인 반영 → 인코딩 → 50KB 초과 시 스펙 절단 사다리 적용
function finalizeCode(master, includeCaptions) {
  var data = JSON.parse(JSON.stringify(master));
  data.peaks.story.forEach(function (p) {
    p.captions = includeCaptions ? p.captions.map(sanitizeCaption).filter(Boolean) : [];
  });
  data.truncated = false;

  return encodeRewind(data).then(function (code) {
    if (code.length <= SIZE_LIMIT) return { code: code, data: data };
    // ① relations 각 배열을 상한의 절반으로
    data.truncated = true;
    halveRelations(data.relations);
    return encodeRewind(data).then(function (code2) {
      if (code2.length <= SIZE_LIMIT) return { code: code2, data: data };
      // ② 캡션 8개로
      data.peaks.story.forEach(function (p) { p.captions = p.captions.slice(0, 8); });
      return encodeRewind(data).then(function (code3) {
        if (code3.length <= SIZE_LIMIT) return { code: code3, data: data };
        // ③ relations는 totals만 남기고 빈 배열
        Object.keys(CAPS).forEach(function (k) {
          if (Array.isArray(data.relations[k])) data.relations[k] = [];
        });
        return encodeRewind(data).then(function (code4) {
          return { code: code4, data: data };
        });
      });
    });
  });
}

/* ---------------- 메인 ---------------- */

var MASTER = null;   // 조립 완료 원본 (캡션 토글 재인코딩용)
var HEALTH = null;

function convert(files, includeCaptions) {
  var st = newState();
  LANG.ko = 0; LANG.en = 0;
  MASTER = null; HEALTH = null;

  var totalBytes = 0;
  files.forEach(function (f) { totalBytes += f.size; });
  progress({ stage: 'unzip', bytes: 0, total: totalBytes, dmThreads: 0, dmMsgs: 0 }, true);

  // 분할 zip: 여러 파일 순차 누적 병합 후 1회 조립
  var chain = Promise.resolve();
  var baseBytes = 0;
  files.forEach(function (f) {
    chain = chain.then(function () {
      return streamZip(f, st, baseBytes, totalBytes).catch(function (streamErr) {
        if (streamErr && streamErr.kind) throw streamErr;
        // 스트리밍 해제 실패 → 크기 제한 내에서 버퍼 방식 재시도
        return bufferZip(f, st);
      }).then(function () { baseBytes += f.size; });
    });
  });

  return chain.then(function () {
    if (st.htmlSeen === 0 && st.jsonSeen > 0) {
      postMessage({ type: 'error', kind: 'json-export' });
      return null;
    }
    if (st.htmlSeen === 0) {
      postMessage({ type: 'error', kind: 'not-instagram' });
      return null;
    }

    progress({ stage: 'connections' }, true);
    var conn = buildConnections(st);

    progress({ stage: 'likes' }, true);
    var likes = buildLikes(st);

    progress({ stage: 'stories' }, true);
    var stories = buildStories(st);
    var storyLikes = buildStoryLikes(st);

    progress({ stage: 'dm', dmThreads: st.prog.dmThreads, dmMsgs: st.prog.dmMsgs }, true);
    var profile = buildProfile(st);
    var dm = buildDm(st, profile);

    progress({ stage: 'assemble' }, true);
    var lang = detectLang(st);
    HEALTH = buildHealth(st, conn.stats, likes, storyLikes, stories, dm);
    HEALTH.lang = lang;
    MASTER = assemble(st, conn, likes, storyLikes, stories, dm, profile, lang);

    progress({ stage: 'encode' }, true);
    return finalizeCode(MASTER, includeCaptions).then(function (r) {
      postMessage({
        type: 'done',
        code: r.code,
        size: r.code.length,
        data: r.data,
        truncated: r.data.truncated,
        health: HEALTH
      });
    });
  });
}

onmessage = function (ev) {
  var msg = ev.data;
  if (!msg) return;
  if (msg.type === 'convert' && msg.files && msg.files.length) {
    convert(msg.files, msg.includeCaptions !== false).catch(function (e) {
      postMessage({ type: 'error', kind: (e && e.kind) || 'fatal', message: String((e && e.message) || e) });
    });
  } else if (msg.type === 'reencode' && MASTER) {
    // 캡션 옵트인 토글 등 재인코딩 (재파싱 없음)
    finalizeCode(MASTER, msg.includeCaptions !== false).then(function (r) {
      postMessage({
        type: 'reencoded',
        code: r.code,
        size: r.code.length,
        data: r.data,
        truncated: r.data.truncated,
        health: HEALTH
      });
    }).catch(function (e) {
      postMessage({ type: 'error', kind: 'fatal', message: String((e && e.message) || e) });
    });
  }
};
