// ===== Survival on the Island – engine + UI (single script, strict mode) =====

type Role = 'doctor' | 'fisher' | 'mushroom' | 'soldier' | 'builder';
type EventType = 'fishing' | 'mushroom' | 'building' | 'cannibals';

interface Person { id: number; role: Role; name: string; alive: boolean; }
interface Config {
  counts: Record<Role, number>;
  cannibals: number;
  rounds: number;
  chooser: string;
  customScript?: (EventType | null)[];
}
interface State { people: Person[]; medicine: boolean; round: number; used: number; }

type Say = (step: string, msg: string) => void;
type Rng = () => number;

const ROLES: Role[] = ['doctor', 'fisher', 'mushroom', 'soldier', 'builder'];
const LABEL: Record<Role, string> = { doctor: 'Doctor', fisher: 'Fisherman', mushroom: 'Mushroom picker', soldier: 'Soldier', builder: 'Builder' };
const CAP = { fisher: 5, mushroom: 4, builder: 6 };
const EVENTS: Record<EventType, string> = { fishing: 'Fishing accident', mushroom: 'Mushroom poisoning', building: 'Building accident', cannibals: 'Cannibal attack' };
const EVENT_LIST = Object.keys(EVENTS) as EventType[];
const EVENT_ROLE: Partial<Record<EventType, Role>> = { fishing: 'fisher', mushroom: 'mushroom', building: 'builder' };

const noop: Say = () => {};
const mulberry = (a: number): Rng => () => {
  a |= 0; a = a + 0x6D2B79F5 | 0;
  let t = Math.imul(a ^ a >>> 15, 1 | a);
  t = t + Math.imul(t ^ t >>> 7, 61 | t) ^ t;
  return ((t ^ t >>> 14) >>> 0) / 4294967296;
};

const alive = (s: State, r?: Role) => s.people.filter(p => p.alive && (!r || p.role === r));

function sample<T>(a: T[], n: number, rng: Rng): T[] {
  const c = [...a], o: T[] = [];
  while (o.length < n && c.length) o.push(c.splice(Math.floor(rng() * c.length), 1)[0]);
  return o;
}
const names = (a: Person[]) => a.map(p => p.name).join(', ') || 'nobody';

type Agg = (v: number[]) => number;
type C = number[];

const binom = (n: number, k: number) => {
  if (k < 0 || k > n) return 0;
  let r = 1;
  for (let i = 1; i <= k; i++) r = r * (n - k + i) / i;
  return r;
};

// Solver for Vicious (Minimax)
function makeSolver(cfg: Config, agg: Agg) {
  const memo = new Map<string, number>(), R = cfg.rounds;
  const mz = (k: string, f: () => number) => {
    let v = memo.get(k);
    if (v === undefined) { v = f(); memo.set(k, v); }
    return v;
  };

  const sub = (c: C, i: number, k = 1) => { const d = [...c]; d[i] -= k; return d; };
  const sum = (c: C) => c[0] + c[1] + c[2] + c[3] + c[4];
  const key = (t: string, c: C, m: number, r: number, u: number, x: string | number = '') => `${t}${c.join(',')}|${m}|${r}|${u}|${x}`;

  const comps = (c: C, k: number) => {
    const out: { p: number; kill: C }[] = [], tot = binom(sum(c), k);
    if (tot === 0) return [{ p: 1, kill: [0, 0, 0, 0, 0] }];
    const rec = (i: number, left: number, kill: C, w: number) => {
      if (i === 5) { if (!left) out.push({ p: w / tot, kill: [...kill] }); return; }
      for (let x = 0; x <= Math.min(c[i], left); x++) {
        kill[i] = x; rec(i + 1, left - x, kill, w * binom(c[i], x));
      }
    };
    rec(0, k, [0, 0, 0, 0, 0], 1);
    return out;
  };

  const outcomes = (c: C, e: EventType) => {
    const rl = EVENT_ROLE[e];
    if (rl) { const i = ROLES.indexOf(rl); return [{ p: 1, kill: [0, 0, 0, 0, 0], idx: i, inj: Math.min(2, c[i]) }]; }
    const k = Math.min(Math.max(0, cfg.cannibals - c[3]), sum(c));
    return comps(c, k).map(x => ({ p: x.p, kill: x.kill, idx: 3, inj: Math.min(Math.min(2, c[3]), c[3] - x.kill[3]) }));
  };

  const V = (c: C, m: number, r: number, u: number): number =>
    r > R ? sum(c) : sum(c) === 0 ? 0 : mz(key('V', c, m, r, u), () => Math.max(...sacOpts(c, m, r, u).map(o => o.v)));

  const sacOpts = (c: C, m: number, r: number, u: number) =>
    [0, 1, 2, 3, 4].filter(i => c[i] > 0).map(i => ({ i, v: A(sub(c, i), m, r, u) }));

  const A = (c: C, m: number, r: number, u: number): number => {
    const n = sum(c); if (!n) return 0;
    const short = 6 * c[4] < n;
    return 5 * c[1] + 4 * c[2] < n
      ? [0, 1, 2, 3, 4].reduce((t, i) => t + (c[i] ? c[i] / n * B(sub(c, i), m, r, u, short) : 0), 0)
      : B(c, m, r, u, short);
  };

  const B = (c: C, m: number, r: number, u: number, short: boolean): number => {
    const n = sum(c); if (!n) return 0;
    if (!short) return E(c, m, r, u);
    return [0, 1, 2, 3, 4].reduce((t, i) => {
      if (!c[i]) return t;
      const o = shelter(c, i, m, r, u); return t + c[i] / n * Math.max(o.die, o.use);
    }, 0);
  };

  const shelter = (c: C, i: number, m: number, r: number, u: number) => ({
    die: E(sub(c, i), m, r, u), use: m && c[0] > 0 ? E(c, 0, r, u) : -1
  });

  const E = (c: C, m: number, r: number, u: number): number => {
    if (!sum(c)) return 0;
    const v = evVals(c, m, r, u).filter(x => !isNaN(x));
    return v.length ? agg(v) : V(c, m, r + 1, u);
  };

  const evVals = (c: C, m: number, r: number, u: number) =>
    EVENT_LIST.map((e, k) => (u >> k & 1) ? NaN : mz(key('F', c, m, r, u, e), () =>
      outcomes(c, e).reduce((t, o) => {
        const q = evOpts(c, m, r, u | 1 << k, o.kill, o.idx, o.inj);
        return t + o.p * Math.max(q.no, q.use);
      }, 0)));

  const evOpts = (c: C, m: number, r: number, u2: number, kill: C, idx: number, inj: number) => {
    const base = c.map((x, i) => x - kill[i]);
    return { no: V(sub(base, idx, inj), m, r + 1, u2), use: m && c[0] > 0 && inj > 0 ? V(base, 0, r + 1, u2) : -1 };
  };

  return { V, sacOpts, shelter, evVals, evOpts };
}

// Solver for Fixed Known Events (Expectimax)
function makeFixedSolver(cfg: Config, script: EventType[]) {
  const memo = new Map<string, number>(), R = cfg.rounds;
  const mz = (k: string, f: () => number) => {
    let v = memo.get(k);
    if (v === undefined) { v = f(); memo.set(k, v); }
    return v;
  };

  const sub = (c: C, i: number, k = 1) => { const d = [...c]; d[i] -= k; return d; };
  const sum = (c: C) => c[0] + c[1] + c[2] + c[3] + c[4];
  const key = (t: string, c: C, m: number, r: number, x: string | number = '') => `${t}${c.join(',')}|${m}|${r}|${x}`;

  const comps = (c: C, k: number) => {
    const out: { p: number; kill: C }[] = [], tot = binom(sum(c), k);
    if (tot === 0) return [{ p: 1, kill: [0, 0, 0, 0, 0] }];
    const rec = (i: number, left: number, kill: C, w: number) => {
      if (i === 5) { if (!left) out.push({ p: w / tot, kill: [...kill] }); return; }
      for (let x = 0; x <= Math.min(c[i], left); x++) {
        kill[i] = x; rec(i + 1, left - x, kill, w * binom(c[i], x));
      }
    };
    rec(0, k, [0, 0, 0, 0, 0], 1);
    return out;
  };

  const outcomes = (c: C, e: EventType) => {
    const rl = EVENT_ROLE[e];
    if (rl) { const i = ROLES.indexOf(rl); return [{ p: 1, kill: [0, 0, 0, 0, 0], idx: i, inj: Math.min(2, c[i]) }]; }
    const k = Math.min(Math.max(0, cfg.cannibals - c[3]), sum(c));
    return comps(c, k).map(x => ({ p: x.p, kill: x.kill, idx: 3, inj: Math.min(Math.min(2, c[3]), c[3] - x.kill[3]) }));
  };

  const V = (c: C, m: number, r: number): number =>
    r > R ? sum(c) : sum(c) === 0 ? 0 : mz(key('V', c, m, r), () => Math.max(...sacOpts(c, m, r).map(o => o.v)));

  const sacOpts = (c: C, m: number, r: number) =>
    [0, 1, 2, 3, 4].filter(i => c[i] > 0).map(i => ({ i, v: A(sub(c, i), m, r) }));

  const A = (c: C, m: number, r: number): number => {
    const n = sum(c); if (!n) return 0;
    const short = 6 * c[4] < n;
    return 5 * c[1] + 4 * c[2] < n
      ? [0, 1, 2, 3, 4].reduce((t, i) => t + (c[i] ? c[i] / n * B(sub(c, i), m, r, short) : 0), 0)
      : B(c, m, r, short);
  };

  const B = (c: C, m: number, r: number, short: boolean): number => {
    const n = sum(c); if (!n) return 0;
    if (!short) return E(c, m, r);
    return [0, 1, 2, 3, 4].reduce((t, i) => {
      if (!c[i]) return t;
      const o = shelter(c, i, m, r); return t + c[i] / n * Math.max(o.die, o.use);
    }, 0);
  };

  const shelter = (c: C, i: number, m: number, r: number) => ({
    die: E(sub(c, i), m, r), use: m && c[0] > 0 ? E(c, 0, r) : -1
  });

  const E = (c: C, m: number, r: number): number => {
    if (!sum(c)) return 0;
    const e = script[r - 1];
    return mz(key('F', c, m, r, e), () => outcomes(c, e).reduce((t, o) => {
      const q = evOpts(c, m, r, o.kill, o.idx, o.inj);
      return t + o.p * Math.max(q.no, q.use);
    }, 0));
  };

  const evOpts = (c: C, m: number, r: number, kill: C, idx: number, inj: number) => {
    const base = c.map((x, i) => x - kill[i]);
    return { no: V(sub(base, idx, inj), m, r + 1), use: m && c[0] > 0 && inj > 0 ? V(base, 0, r + 1) : -1 };
  };

  return { V, sacOpts, shelter, evOpts };
}

type Solver = ReturnType<typeof makeSolver>;
type FixedSolver = ReturnType<typeof makeFixedSolver>;

const cnt = (s: State): C => ROLES.map(r => alive(s, r).length);
const fx = (v: number) => v.toFixed(2);
const mm = (x: Ctx) => x.st.medicine ? 1 : 0;

interface Scratch { n: number; food: number; shelter: number; c0: C; injured: Person[]; killed: Person[]; }
interface Ctx { st: State; s: Scratch; }
type Opp = (x: Ctx, e: Env) => { ev: EventType; note?: string };
interface Brain {
  sacrifice(x: Ctx, e: Env): { p: Person; note: string };
  shelter(x: Ctx, e: Env, v: Person): { use: boolean; note: string };
  doctor(x: Ctx, e: Env): { use: boolean; note: string };
}
interface Env { cfg: Config; brain: Brain; opp: Opp; rollOpp: Opp; rng: Rng; say: Say; }

const T1 = '1 · Sacrifice', T3 = '3 · Resource check', T4 = '4 · Monthly event', T5 = "5 · Doctor's decision", T6 = '6 · Casualties';
const byId = (x: Ctx, p: Person) => x.st.people.find(q => q.id === p.id)!;

const STEPS: ((x: Ctx, e: Env) => void)[] = [
  (x, e) => { const d = e.brain.sacrifice(x, e); e.say(T1, d.note); d.p.alive = false; e.say(T1, `${d.p.name} is sacrificed.`); },
  (x, e) => {
    const s = x.s, A = (r: Role) => alive(x.st, r).length;
    s.n = alive(x.st).length; s.food = 5 * A('fisher') + 4 * A('mushroom'); s.shelter = 6 * A('builder');
    e.say('2 · Work', `${s.n} workers left. Food for ${s.food} (${A('fisher')}×5 fish + ${A('mushroom')}×4 mushrooms), shelter for ${s.shelter} (${A('builder')}×6), ${A('soldier')} soldier(s) on guard.`);
  },
  (x, e) => {
    const s = x.s;
    if (s.food < s.n) {
      const v = sample(alive(x.st), 1, e.rng)[0];
      if (v) { v.alive = false; e.say(T3, `Food shortage (${s.food} < ${s.n}): ${v.name} starves. Medicine cannot help.`); }
    } else e.say(T3, `Food sufficient (${s.food} ≥ ${s.n}).`);

    if (s.shelter >= s.n) { e.say(T3, `Shelter sufficient (${s.shelter} ≥ ${s.n}).`); return; }
    const v = sample(alive(x.st), 1, e.rng)[0]; if (!v) return;
    e.say(T3, `Shelter shortage (${s.shelter} < ${s.n}): ${v.name} is injured by exposure.`);
    if (x.st.medicine && alive(x.st, 'doctor').length) {
      const d = e.brain.shelter(x, e, v); e.say(T3, d.note);
      if (d.use) { x.st.medicine = false; e.say(T3, `${v.name} is saved; medicine is gone.`); return; }
    }
    v.alive = false; e.say(T3, `${v.name} dies of exposure.`);
  },
  (x, e) => {
    const s = x.s; s.c0 = cnt(x.st); const o = e.opp(x, e); if (o.note) e.say(T4, o.note);
    e.say(T4, `${EVENTS[o.ev]}.`); x.st.used |= 1 << EVENT_LIST.indexOf(o.ev);
    s.killed = []; s.injured = [];
    const role = EVENT_ROLE[o.ev];
    if (role) {
      s.injured = sample(alive(x.st, role), 2, e.rng); e.say(T4, `Injured: ${names(s.injured)}.`);
    } else {
      const sol = s.c0[3], k = Math.min(Math.max(0, e.cfg.cannibals - sol), alive(x.st).length);
      e.say(T4, `${e.cfg.cannibals} cannibals attack, ${sol} soldier(s) defend → ${k} break through.`);
      s.killed = sample(alive(x.st), k, e.rng);
      if (k) e.say(T4, `Mortally wounded: ${names(s.killed)}.`);
      s.injured = sample(alive(x.st, 'soldier').filter(p => !s.killed.includes(p)), Math.min(2, sol), e.rng);
      if (sol) e.say(T4, `Injured defenders: ${names(s.injured)}.`);
    }
  },
  (x, e) => {
    const s = x.s;
    if (!s.injured.length) e.say(T5, 'Nobody injured by this event – nothing to treat.');
    else if (!x.st.medicine) e.say(T5, 'Medicine already used – injured cannot be saved.');
    else if (!alive(x.st, 'doctor').length) e.say(T5, 'Doctor is dead – medicine is lost.');
    else {
      const d = e.brain.doctor(x, e); e.say(T5, d.note);
      if (d.use) { x.st.medicine = false; e.say(T5, `${names(s.injured)} saved; medicine is gone.`); s.injured = []; }
    }
  },
  (x, e) => { const dead = [...x.s.killed, ...x.s.injured]; dead.forEach(p => p.alive = false); e.say(T6, dead.length ? `Dead: ${names(dead)}.` : 'No casualties this event.'); },
  (x, e) => e.say('7 · End of round', 'Storms destroy shelters; fish, mushrooms and all other food spoil. Nothing carries over.')
];

function finish(x: Ctx, e: Env, i: number) {
  for (; i < STEPS.length; i++) STEPS[i](x, e);
  x.st.round++;
  while (x.st.round <= e.cfg.rounds && alive(x.st).length) {
    STEPS.forEach(f => f(x, e)); x.st.round++;
  }
}

function heur(st: State, cfg: Config, rng: Rng): Person {
  let best = alive(st)[0], bp = 1e9; const n = alive(st).length - 1;
  for (const r of ROLES) {
    const g = alive(st, r); if (!g.length) continue;
    const c = (y: Role) => alive(st, y).length - (y === r ? 1 : 0);
    const pen = (CAP.fisher * c('fisher') + CAP.mushroom * c('mushroom') < n ? 10 : 0) + (CAP.builder * c('builder') < n ? 10 : 0) + Math.max(0, cfg.cannibals - c('soldier')) * 3 + (r === 'doctor' && st.medicine ? 2 : 0) + rng() * .5;
    if (pen < bp) { bp = pen; best = g[0]; }
  }
  return best;
}

const DEFAULT: Brain = {
  sacrifice: (x, e) => ({ p: heur(x.st, e.cfg, e.rng), note: '' }),
  shelter: () => ({ use: false, note: '' }),
  doctor: (x, e) => { const n = x.s.injured.length; return { use: n >= 2 || (n >= 1 && x.st.round === e.cfg.rounds), note: '' }; }
};

function evalOption(x: Ctx, e: Env, apply: (c: Ctx) => void, from: number, K = 200) {
  let t = 0; const base = Math.floor(e.rng() * 2 ** 30);
  for (let k = 0; k < K; k++) {
    const c = structuredClone(x); apply(c);
    finish(c, { ...e, brain: DEFAULT, opp: e.rollOpp, say: noop, rng: mulberry(base + k) }, from);
    t += alive(c.st).length;
  }
  return t / K;
}

const mcBrain: Brain = {
  sacrifice: (x, e) => {
    const sc = ROLES.map(r => ({ r, p: alive(x.st, r)[0] })).filter(o => o.p).map(o => ({ ...o, v: evalOption(x, e, c => { byId(c, o.p).alive = false; }, 1) }));
    const b = sc.reduce((a, c) => c.v > a.v + 1e-9 ? c : a);
    return { p: b.p, note: 'Monte-Carlo estimate of expected survivors if sacrificing: ' + sc.map(o => `${LABEL[o.r]} ${fx(o.v)}`).join(' · ') };
  },
  shelter: (x, e, v) => {
    const u = evalOption(x, e, c => { c.st.medicine = false; }, 3), d = evalOption(x, e, c => { byId(c, v).alive = false; }, 3);
    return { use: u > d + 1e-9, note: `Doctor weighs (Monte Carlo): spend medicine on ${v.name} now ${fx(u)} vs save it ${fx(d)}.` };
  },
  doctor: (x, e) => {
    const u = evalOption(x, e, c => { c.st.medicine = false; c.s.injured = []; }, 5), k = evalOption(x, e, () => {}, 5);
    return { use: u > k + 1e-9, note: `Doctor weighs (Monte Carlo): use medicine ${fx(u)} vs keep it ${fx(k)}.` };
  }
};

const exactBrain = (S: Solver): Brain => ({
  sacrifice: x => {
    const o = S.sacOpts(cnt(x.st), mm(x), x.st.round, x.st.used), b = o.reduce((a, c) => c.v > a.v + 1e-9 ? c : a);
    return { p: alive(x.st, ROLES[b.i])[0], note: 'Minimax value (expected survivors) if sacrificing: ' + o.map(q => `${LABEL[ROLES[q.i]]} ${fx(q.v)}`).join(' · ') };
  },
  shelter: (x, e, v) => {
    const o = S.shelter(cnt(x.st), ROLES.indexOf(v.role), mm(x), x.st.round, x.st.used);
    return { use: o.use > o.die + 1e-9, note: `Doctor weighs: spend medicine now ${fx(o.use)} vs save it ${fx(o.die)}.` };
  },
  doctor: x => {
    const s = x.s, n = s.injured.length, kv = ROLES.map(r => s.killed.filter(p => p.role === r).length);
    const o = S.evOpts(s.c0, mm(x), x.st.round, x.st.used, kv, n ? ROLES.indexOf(s.injured[0].role) : 3, n);
    return { use: o.use > o.no + 1e-9, note: `Doctor weighs: use medicine ${fx(o.use)} vs keep it ${fx(o.no)}.` };
  }
});

const fixedExactBrain = (S: FixedSolver): Brain => ({
  sacrifice: x => {
    const o = S.sacOpts(cnt(x.st), mm(x), x.st.round), b = o.reduce((a, c) => c.v > a.v + 1e-9 ? c : a);
    return { p: alive(x.st, ROLES[b.i])[0], note: 'Exact expectimax value if sacrificing: ' + o.map(q => `${LABEL[ROLES[q.i]]} ${fx(q.v)}`).join(' · ') };
  },
  shelter: (x, e, v) => {
    const o = S.shelter(cnt(x.st), ROLES.indexOf(v.role), mm(x), x.st.round);
    return { use: o.use > o.die + 1e-9, note: `Doctor weighs: spend medicine now ${fx(o.use)} vs save it ${fx(o.die)}.` };
  },
  doctor: x => {
    const s = x.s, n = s.injured.length, kv = ROLES.map(r => s.killed.filter(p => p.role === r).length);
    const o = S.evOpts(s.c0, mm(x), x.st.round, kv, n ? ROLES.indexOf(s.injured[0].role) : 3, n);
    return { use: o.use > o.no + 1e-9, note: `Doctor weighs: use medicine ${fx(o.use)} vs keep it ${fx(o.no)}.` };
  }
});

const viciousOpp = (S: Solver): Opp => x => {
  const v = S.evVals(cnt(x.st), mm(x), x.st.round, x.st.used);
  let b = -1; v.forEach((q, i) => { if (!isNaN(q) && (b < 0 || q < v[b])) b = i; });
  if (b < 0) b = 0;
  return { ev: EVENT_LIST[b], note: 'Opponent minimises (unused events only) – expected survivors: ' + EVENT_LIST.map((q, i) => `${EVENTS[q]} ${isNaN(v[i]) ? 'used' : fx(v[i])}`).join(' · ') };
};

const uniformOpp: Opp = (x, e) => {
  const pool = EVENT_LIST.filter((_, k) => !(x.st.used >> k & 1));
  const p = pool.length ? pool : EVENT_LIST;
  return { ev: p[Math.floor(e.rng() * p.length)] };
};
const scriptOpp = (sc: EventType[]): Opp => x => ({ ev: sc[x.st.round - 1] });

function getCustomScript(cfg: Config, rng: Rng): EventType[] {
  const rounds = cfg.rounds;
  const drawn = sample(EVENT_LIST, rounds, rng);
  const custom = cfg.customScript || [];
  const used = new Set<EventType>();
  const result: (EventType | null)[] = [];

  for (let i = 0; i < rounds; i++) {
    let ev = custom[i];
    if (ev && EVENT_LIST.includes(ev) && !used.has(ev)) {
      used.add(ev); result.push(ev);
    } else { result.push(null); }
  }
  const remaining = EVENT_LIST.filter(e => !used.has(e));
  for (let i = 0; i < rounds; i++) {
    if (!result[i]) result[i] = remaining.shift() || drawn[i];
  }
  return result as EventType[];
}

interface Mode {
  label: string;
  make: (cfg: Config, rng: Rng) => { brain: Brain; opp: Opp; rollOpp: Opp; script?: EventType[]; solver?: Solver | FixedSolver };
}

const MODES: Record<string, Mode> = {
  vicious: { label: 'Vicious – minimax on both sides (exact)', make: cfg => { const S = makeSolver(cfg, v => Math.min(...v)); return { brain: exactBrain(S), opp: viciousOpp(S), rollOpp: uniformOpp, solver: S }; } },
  random: { label: 'Random events – island unaware (Monte Carlo)', make: () => ({ brain: mcBrain, opp: uniformOpp, rollOpp: uniformOpp }) },
  'fixed-known': { label: 'Predestined events – island knows them (exact expectimax)', make: (c, r) => { const sc = getCustomScript(c, r); const S = makeFixedSolver(c, sc); return { brain: fixedExactBrain(S), opp: scriptOpp(sc), rollOpp: scriptOpp(sc), script: sc, solver: S }; } },
  'fixed-hidden': { label: 'Predestined events – island unaware (Monte Carlo)', make: (c, r) => { const sc = getCustomScript(c, r); return { brain: mcBrain, opp: scriptOpp(sc), rollOpp: uniformOpp, script: sc }; } },
};

interface RoundReport { round: number; before: number; after: number; steps: { title: string; lines: string[] }[]; }

function simulate(cfg0: Config) {
  const cfg = { ...cfg0, rounds: Math.min(4, Math.max(1, cfg0.rounds)) };
  const rng = mulberry(Date.now() & 0x7fffffff);
  let id = 0;
  const st: State = { people: [], medicine: true, round: 1, used: 0 };
  for (const r of ROLES) for (let i = 1; i <= cfg.counts[r]; i++) st.people.push({ id: id++, role: r, name: `${LABEL[r]} ${i}`, alive: true });
  const total = st.people.length, reports: RoundReport[] = [], md = MODES[cfg.chooser].make(cfg, rng);
  const x: Ctx = { st, s: { n: 0, food: 0, shelter: 0, c0: [], injured: [], killed: [] } };
  const plan = md.solver ? (cfg.chooser === 'fixed-known' ? (md.solver as FixedSolver).V(cnt(st), 1, 1) : (md.solver as Solver).V(cnt(st), 1, 1, 0)) : null;

  for (; st.round <= cfg.rounds && alive(st).length; st.round++) {
    const rep: RoundReport = { round: st.round, before: alive(st).length, after: 0, steps: [] };
    const say: Say = (t, m) => { let s = rep.steps.find(q => q.title === t); if (!s) rep.steps.push(s = { title: t, lines: [] }); s.lines.push(m); };
    const e: Env = { cfg, brain: md.brain, opp: md.opp, rollOpp: md.rollOpp, rng, say };
    STEPS.forEach(f => f(x, e));
    rep.after = alive(st).length;
    reports.push(rep);
  }
  return { reports, survivors: alive(st), total, plan, script: md.script };
}