#!/usr/bin/env node
/* Petri Dash Vault: curation analysis.
   Reads every saved session, weighs each player by the calibration rounds, tallies the votes on each entry per game type, and writes
   which entries are ready for a curation decision. It proposes; it changes nothing in the Atlas.

   node analyze.js --dump <dir with sessions/<uid>/reports/<start>.json> --index <curation_index.json> --out <dir> [--date YYYY-MM-DD]
                   [--records <file.json: [{uid, session, rec}]>] [--mask <file.json: ["dataset:entry", ...] treated as having no class yet>] */
"use strict";
const fs = require("fs"), path = require("path");
const arg = k => { const i = process.argv.indexOf("--" + k); return i > 0 ? process.argv[i + 1] : null; };
const CHANCE = { O: 0.5, G: 0.6, N: 0.2, M: 0.3 };          // what answering at random scores on confirmed material, measured with a random player over 1,000 rounds
const GOLD_ND = 20, MIN_T = 3, NEED_SESSIONS = 3, SHARE = 0.75, SHARE_M = 0.6, PRIOR_N = 2, GATE_N = 6, GATE_SKILL = 0.15;
const GAME = { M: "Model", O: "Drag-on-Like", G: "Group sort", N: "Name it" };

/* ---------------------------------------------------------------- input */
const index = JSON.parse(fs.readFileSync(arg("index"), "utf8")).datasets;
const mask = new Set(arg("mask") ? JSON.parse(fs.readFileSync(arg("mask"), "utf8")) : []);
const info = (ps, id) => { const d = index[ps], e = d && d.entries[id]; return e ? { cls: e[0], nm: e[1], conf: !!e[2], nd: e[3], why: e[4], q: e[5], model: !!e[6] } : null; };
const sessions = [];
(function walk(dir) {
  if (!dir || !fs.existsSync(dir)) return;
  for (const f of fs.readdirSync(dir)) { const p = path.join(dir, f), st = fs.statSync(p);
    if (st.isDirectory()) walk(p);
    else { const m = /sessions[\/\\]([^\/\\]+)[\/\\]reports[\/\\]([^\/\\]+)\.json$/.exec(p); if (!m) continue;
      try { const d = JSON.parse(fs.readFileSync(p, "utf8")), rec = d.rec || (d.data && d.data.rec); if (rec && Array.isArray(rec.rounds)) sessions.push({ uid: m[1], session: m[1] + ":" + m[2], rec }); } catch (e) { } } }
})(arg("dump"));
if (arg("records")) JSON.parse(fs.readFileSync(arg("records"), "utf8")).forEach(x => sessions.push(x));

/* ---------------------------------------------------------------- calibration: how much weight each player's answers deserve */
function pairCtl(labels, grp) {
  let st = 0, sn = 0, dt = 0, dn = 0;
  for (let i = 0; i < labels.length; i++) for (let j = i + 1; j < labels.length; j++) { if (labels[i] == null || labels[j] == null) continue; const tog = grp[i] === grp[j]; if (labels[i] === labels[j]) { sn++; if (tog) st++; } else { dn++; if (!tog) dt++; } }
  return sn && dn ? (st / sn + dt / dn) / 2 : null;
}
const groupIndex = (groups, ids) => ids.map(id => groups.findIndex(g => g.includes(id)));
function controlOf(r) {                                     // newer sessions save the score; for older ones it is rebuilt from what the round held
  if (r.ctl && r.ctl.score != null) return { score: r.ctl.score, gold: !!r.ctl.gold };
  if (r.ctl === null && r.sys) return null;                 // a newer round that carried no confirmed material
  if (r.type === "N") { const e = info(r.ps, r.entry || r.focus); return r.calib && r.calib.seeded && e && e.conf && e.nd <= GOLD_ND ? { score: r.calib.agree ? 1 : 0, gold: false } : null; }
  if (r.type === "O" && r.entries && r.groups && r.target) { const ids = r.entries.map(x => x.id), labs = ids.map(id => { if (id === r.focus) return null; const e = info(r.ps, id); return !e || !e.conf ? null : e.nm === r.target ? "C" : "x:" + e.nm; });
    const s = pairCtl(labs, groupIndex(r.groups, ids)); return s == null ? null : { score: s, gold: false }; }
  if (r.type === "G" && r.groups) { const ids = [].concat(...r.groups), labs = ids.map(id => { if (id === r.focus) return null; const e = info(r.ps, id); return e && e.conf ? e.nm : null; });
    const s = pairCtl(labs, groupIndex(r.groups, ids)); return s == null ? null : { score: s, gold: false }; }
  return null;
}
const rel = {};                                             // uid -> type -> { n, sum (skill), raw (score) }
for (const s of sessions) for (const r of s.rec.rounds) { if (r.skipped) continue; const c = controlOf(r); if (!c) continue;
  const t = ((rel[s.uid] = rel[s.uid] || {})[r.type] = rel[s.uid][r.type] || { n: 0, sum: 0, raw: 0, gold: 0 });
  t.n++; t.raw += c.score; if (c.gold) t.gold++; }
const skill = (t, type) => Math.max(0, Math.min(1, (t.raw / t.n - CHANCE[type]) / (1 - CHANCE[type])));     // 0 at chance, 1 when every answer agrees with the confirmed material
function weight(uid, type) {                                // a weak prior of 0.5 until calibration rounds say otherwise; a player who stays at chance counts for nothing
  if (process.argv.includes("--noweight")) return 1;        // for testing: every answer counts in full, calibration ignored
  const u = rel[uid] || {}, t = u[type]; let n = 0, sk = 0;
  if (t && t.n >= 2) { n = t.n; sk = skill(t, type); } else Object.keys(u).forEach(k => { sk = (sk * n + skill(u[k], k) * u[k].n) / (n + u[k].n); n += u[k].n; });   // too few rounds in this game: all games together
  if (n >= GATE_N && sk < GATE_SKILL) return 0;
  return (sk * n + 0.5 * PRIOR_N) / (n + PRIOR_N);
}

/* ---------------------------------------------------------------- votes: one per session, per entry, per game type */
const ent = {};                                             // "dataset:entry" -> evidence record
const rec = key => ent[key] = ent[key] || { key, ps: key.split(":")[0], id: key.split(":").slice(1).join(":"), appearances: 0, games: {} };
function vote(key, type, session, uid, answer, w, extra) {
  const g = (rec(key).games[type] = rec(key).games[type] || { votes: new Map() });
  if (!g.votes.has(session)) g.votes.set(session, { uid, answer, w, extra });      // a session votes once on an entry in a game type
}
let answered = 0, skipped = 0, fast = 0, golds = 0;
for (const s of sessions) for (const r of s.rec.rounds) {
  if (r.skipped) { skipped++; continue; } answered++;
  if (r.gold) { golds++; continue; }                        // calibration rounds weigh the player; they are not votes
  if (!r.focus) continue; const key = r.ps + ":" + r.focus; rec(key).appearances++;
  if ((r.t || 0) < MIN_T) { fast++; continue; }
  const w = weight(s.uid, r.type);
  if (r.type === "N") vote(key, "N", s.session, s.uid, r.chosen === "none of these" ? "none" : "fam:" + r.chosen, w * (r.hint ? 0.5 : 1) * (r.sure === false ? 0.7 : 1), { suggest: r.suggest || "" });
  else if (r.type === "O" && r.groups && r.entries) {
    const mine = r.groups.find(g => g.includes(r.focus)) || [r.focus], cons = r.entries.filter(x => x.id !== r.focus && (x.role ? x.role === "in" : (info(r.ps, x.id) || {}).nm === r.target)).map(x => x.id);
    const withCons = cons.filter(id => mine.includes(id)).length, others = mine.filter(id => id !== r.focus && !cons.includes(id)).map(id => (info(r.ps, id) || {}).nm).filter(Boolean);
    let a; if (cons.length && withCons >= cons.length / 2) a = "fam:" + r.target; else if (others.length && withCons === 0) { const c = {}; others.forEach(n => c[n] = (c[n] || 0) + 1); a = "fam:" + Object.keys(c).sort((x, y) => c[y] - c[x])[0]; } else a = "not:" + r.target;
    if (r.target) vote(key, "O", s.session, s.uid, a, w, {});
  } else if (r.type === "G" && r.groups) {
    const mine = (r.groups.find(g => g.includes(r.focus)) || []).filter(id => id !== r.focus), c = {}; mine.forEach(id => { const e = info(r.ps, id); if (e && e.conf) c[e.nm] = (c[e.nm] || 0) + 1; });
    const top = Object.keys(c).sort((x, y) => c[y] - c[x])[0];
    vote(key, "G", s.session, s.uid, !mine.length ? "none" : top && c[top] >= 2 && c[top] / mine.length >= 0.6 ? "fam:" + top : "mixed", w, {});
  } else if (r.type === "M") {
    const nC = (r.flagCand || []).reduce((a, x) => a + x.n, 0), nR = (r.flagRef || []).reduce((a, x) => a + x.n, 0);
    vote(key, "M", s.session, s.uid, nC + nR < 8 ? "matches" : "differs", w, { ref: r.ref, cross: !!r.cross, cols: (r.flagCand || []).map(x => [x.c0, x.c1]) });
  }
}

/* ---------------------------------------------------------------- agreement, note levels, proposals */
function tally(g, type) {
  const by = {}; let tot = 0; g.votes.forEach(v => { by[v.answer] = (by[v.answer] || 0) + v.w; tot += v.w; });
  const order = Object.keys(by).sort((a, b) => by[b] - by[a]), lead = order[0], n = g.votes.size, share = tot > 0 ? by[lead] / tot : 0;
  const nLead = [...g.votes.values()].filter(v => v.answer === lead && v.w > 0).length, need = type === "M" ? SHARE_M : SHARE;
  return { n, lead, share, nLead, weight: tot, agreed: nLead >= NEED_SESSIONS && share >= need && lead !== "mixed", near: share >= need && lead !== "mixed" ? Math.max(0, NEED_SESSIONS - nLead) : NEED_SESSIONS, by };
}
const famOf = a => a && a.startsWith("fam:") ? a.slice(4) : null;
function concur(a, b) { const fa = famOf(a), fb = famOf(b); if (fa && fb) return fa === fb ? 1 : -1;
  const neg = x => x === "none" ? "*" : x && x.startsWith("not:") ? x.slice(4) : null, na = neg(a), nb = neg(b);
  if (fa && nb) return nb === "*" || nb === fa ? -1 : 0; if (fb && na) return na === "*" || na === fb ? -1 : 0; if (na && nb) return 1; return 0; }
const out = { ready: [], supported: [], suggested: [], disputed: [], difficult: [], partner: [] };
for (const e of Object.values(ent)) {
  const i = info(e.ps, e.id) || {}, masked = mask.has(e.key); e.now = masked ? "" : i.nm || ""; e.cls = masked ? "" : i.cls || ""; e.nd = i.nd; e.why = i.why || ""; e.title = (index[e.ps] || {}).title || e.ps; e.sys = (index[e.ps] || {}).sys || "";
  const cls = ["N", "O", "G"].filter(t => e.games[t]).map(t => Object.assign({ type: t }, tally(e.games[t], t))); e.tallies = cls; if (e.games.M) e.model = tally(e.games.M, "M");
  const agreed = cls.filter(c => c.agreed); let level = "open", prop = null;
  if (agreed.length >= 2) { let clash = false, pair = null; for (let a = 0; a < agreed.length; a++) for (let b = a + 1; b < agreed.length; b++) { const c = concur(agreed[a].lead, agreed[b].lead); if (c < 0) clash = true; if (c > 0) pair = [agreed[a], agreed[b]]; }
    if (clash) level = "disputed"; else if (pair) { level = "corroborated"; prop = famOf(pair[0].lead) ? pair[0].lead : pair[1].lead; } else { level = "supported"; prop = (agreed.find(c => famOf(c.lead)) || agreed[0]).lead; } }
  else if (agreed.length === 1) { level = "supported"; prop = agreed[0].lead; }
  else if (cls.some(c => c.nLead >= 2 && c.share >= SHARE && c.lead !== "mixed")) { level = "suggested"; prop = cls.find(c => c.nLead >= 2 && c.share >= SHARE).lead; }
  if ((level === "open" || level === "suggested") && e.appearances >= 5) level = "difficult";
  e.level = level; e.prop = prop; const fam = famOf(prop);
  e.action = !prop ? "" : fam ? (fam === e.now ? "confirm " + fam : e.now ? "relabel " + e.now + " to " + fam : "assign to " + fam) : prop === "none" ? "fits none of the families shown: outlier or new family" : "does not fit " + prop.slice(4);
  e.amend = !!prop && !(fam && fam === e.now);
  const m = e.model; if (m && m.agreed && m.lead === "differs") { const cols = [...e.games.M.votes.values()].filter(v => v.answer === "differs").map(v => v.extra.cols).filter(c => c && c.length); e.region = cols.length ? cols[0].map(c => c.join("-")).join(", ") : ""; }
  e.next = level === "supported" ? (agreed[0].type === "N" ? "Drag-on-Like with " + (fam || "the leading family") + " as the conserved set" : i.model ? "Name it or Model" : "Name it") : level === "disputed" ? "Model against references of both families" : cls.length ? GAME[cls.slice().sort((a, b) => a.near - b.near)[0].type] + " with a new player" : "Drag-on-Like";
  out[level === "corroborated" ? "ready" : level] && out[level === "corroborated" ? "ready" : level].push(e);
}
/* partner subunits: the A and B entry of one operon should end up in the same class */
const clsOfFam = (ps, fam) => { const c = {}; Object.values((index[ps] || { entries: {} }).entries).forEach(x => { if (x[1] === fam) c[x[0]] = (c[x[0]] || 0) + 1; }); return Object.keys(c).sort((a, b) => c[b] - c[a])[0] || fam; };
for (const e of Object.values(ent)) { if (!/_A$/.test(e.ps) || !famOf(e.prop) || e.level === "open" || e.level === "suggested") continue; const p = ent[e.ps.replace(/_A$/, "_B") + ":" + e.id];
  if (p && famOf(p.prop) && p.level !== "open" && p.level !== "suggested" && clsOfFam(e.ps, famOf(e.prop)) !== clsOfFam(p.ps, famOf(p.prop))) out.partner.push([e, p]); }

/* ---------------------------------------------------------------- what the game should deal next */
const prio = {};
for (const e of Object.values(ent)) { if (e.level === "corroborated") { prio[e.key] = 0.05; continue; } const near = Math.min(...e.tallies.map(c => c.near), NEED_SESSIONS); if (near < NEED_SESSIONS) prio[e.key] = +(4 / (1 + near)).toFixed(2); }   // closeness 1/(1+votes still needed), relative to an unseen entry

/* ---------------------------------------------------------------- output */
const date = arg("date") || new Date().toISOString().slice(0, 10), outDir = arg("out") || "."; fs.mkdirSync(outDir, { recursive: true });
const pct = x => Math.round(100 * x) + "%", short = u => u.length > 8 ? u.slice(0, 2) + "…" + u.slice(-4) : u;
const evid = e => e.tallies.map(c => GAME[c.type] + ": " + c.n + " session" + (c.n === 1 ? "" : "s") + ", " + pct(c.share) + " " + (famOf(c.lead) || c.lead.replace("not:", "not ")) + (c.agreed ? " (agreed)" : "")).concat(e.model ? ["Model: " + e.model.n + " session" + (e.model.n === 1 ? "" : "s") + ", " + pct(e.model.share) + " " + e.model.lead + (e.region ? ", columns " + e.region : "")] : []).join("; ");
const row = e => "| " + e.id + " | " + e.title + " | " + (e.now || "none") + " | " + (e.action || "-") + " | " + evid(e) + " |";
const table = list => list.length ? ["| Entry | Dataset | Atlas now | Proposal | Evidence |", "|---|---|---|---|---|"].concat(list.sort((a, b) => (b.nd || 0) - (a.nd || 0)).map(row)).join("\n") : "None.";
const players = Object.keys(rel).length, L = [];
L.push("# Atlas curation notes from Petri Dash Vault", "", "Run of " + date + ". " + sessions.length + " sessions read from " + new Set(sessions.map(s => s.uid)).size + " players: " + answered + " rounds answered (" + golds + " calibration rounds), " + skipped + " skipped, " + fast + " answered in under " + MIN_T + " s and not counted as votes. " + Object.keys(ent).length + " entries have at least one vote.", "",
  "Nothing here has been applied to the Atlas. An entry is ready for a decision when at least " + NEED_SESSIONS + " sessions agree (" + pct(SHARE) + " of the weighted votes) in two game types that concur.", "");
L.push("## Ready for a curation decision (" + out.ready.length + ")", "", "Amendments first, then confirmations.", "", table(out.ready.filter(e => e.amend)), "", out.ready.some(e => !e.amend) ? table(out.ready.filter(e => !e.amend)) : "", "");
L.push("## Supported in one game type: a second game type is needed (" + out.supported.length + ")", "", out.supported.length ? ["| Entry | Dataset | Atlas now | Proposal | Evidence | Next game |", "|---|---|---|---|---|---|"].concat(out.supported.map(e => row(e) + " " + e.next + " |")).join("\n") : "None.", "");
L.push("## Disputed between game types (" + out.disputed.length + ")", "", table(out.disputed), "");
L.push("## Difficult to classify: five or more appearances, still unsettled (" + out.difficult.length + ")", "", table(out.difficult), "");
L.push("## Partner subunits called differently (" + out.partner.length + ")", "", out.partner.length ? out.partner.map(([a, b]) => "- " + a.id + ": A subunit " + a.action + "; B subunit " + b.action + ". Review the pair together.").join("\n") : "None.", "");
L.push("## Two sessions agree so far (" + out.suggested.length + ")", "", out.suggested.length ? out.suggested.map(e => "- " + e.id + " (" + e.title + "): " + e.action + ". " + evid(e)).join("\n") : "None.", "");
L.push("## Player reliability", "", "From calibration rounds and other confirmed material. Weight 0 means the answers were no better than chance and are not counted.", "", "| Player | Game | Rounds with confirmed material | Mean score | Chance | Weight |", "|---|---|---|---|---|---|");
Object.keys(rel).sort().forEach(u => Object.keys(rel[u]).sort().forEach(t => L.push("| " + short(u) + " | " + GAME[t] + " | " + rel[u][t].n + " | " + (rel[u][t].raw / rel[u][t].n).toFixed(2) + " | " + CHANCE[t] + " | " + weight(u, t).toFixed(2) + " |")));
L.push("", "## Game scorecard", "", "| Game | Entries with votes | Agreed | Mean sessions per entry |", "|---|---|---|---|");
["N", "O", "G", "M"].forEach(t => { const es = Object.values(ent).filter(e => e.games[t]), ag = es.filter(e => t === "M" ? e.model && e.model.agreed : e.tallies.some(c => c.type === t && c.agreed)); L.push("| " + GAME[t] + " | " + es.length + " | " + ag.length + " | " + (es.length ? (es.reduce((a, e) => a + e.games[t].votes.size, 0) / es.length).toFixed(1) : "0") + " |"); });
fs.writeFileSync(path.join(outDir, "curation_notes.md"), L.join("\n") + "\n");
const slim = e => ({ key: e.key, sys: e.sys, now: e.now, nd: e.nd, level: e.level, proposal: e.prop, action: e.action, amend: e.amend, appearances: e.appearances, tallies: e.tallies.map(c => ({ type: c.type, n: c.n, lead: c.lead, share: +c.share.toFixed(3), nLead: c.nLead, agreed: c.agreed })), model: e.model ? { n: e.model.n, lead: e.model.lead, share: +e.model.share.toFixed(3), agreed: e.model.agreed } : null, next: e.next });
fs.writeFileSync(path.join(outDir, "evidence.json"), JSON.stringify(Object.values(ent).map(slim)));
const relOut = {}; Object.keys(rel).forEach(u => { relOut[u] = {}; Object.keys(rel[u]).forEach(t => relOut[u][t] = { n: rel[u][t].n, mean: +(rel[u][t].raw / rel[u][t].n).toFixed(3), weight: +weight(u, t).toFixed(3) }); });
fs.writeFileSync(path.join(outDir, "reliability.json"), JSON.stringify(relOut));
const top = Object.keys(prio).sort((a, b) => prio[b] - prio[a]).slice(0, 600), prioOut = {}; top.forEach(k => prioOut[k] = prio[k]); Object.keys(prio).filter(k => prio[k] < 1).forEach(k => prioOut[k] = prio[k]);
const state = { date, sessions: sessions.length, players, ready: out.ready.length, amendments: out.ready.filter(e => e.amend).length, supported: out.supported.length, disputed: out.disputed.length, difficult: out.difficult.length, prio: prioOut };
fs.writeFileSync(path.join(outDir, "state.json"), JSON.stringify(state));
console.log(JSON.stringify({ date, sessions: sessions.length, players, answered, calibration: golds, entries: Object.keys(ent).length, ready: out.ready.length, amendments: state.amendments, supported: out.supported.length, suggested: out.suggested.length, disputed: out.disputed.length, difficult: out.difficult.length, partner: out.partner.length }));
