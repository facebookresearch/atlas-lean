/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Karp.HamPathEmitSpec
public import CSLibExt.Computability.Complexity.SatCheck
public import CSLibExt.Computability.Complexity.SatLookup
public import Mathlib.Tactic.Ring

/-!
# SAT ≤ HAMPATH, component 2: the emitter machine and its first phase

A `TM2` machine that reads the token stack `(toks φ).reverse` of
`Cslib.Complexity.SatVerifier` and pushes Sipser's HAMPATH instance `toHam φ` onto the output
stack `O`, so that `O` reads the instance top-first.

* Phase A walks the token stack, moving it onto `F` (where it reads `toks φ`), counts the clauses
  on `C` and `3 m` on `M`, and collects the distinct variables on `V`: a name is new when no
  entry of `V` matches it (`cmpB`), and new names are pushed, so `V` lists `hamVars φ` top-first
  (the token stack is read from the end of the formula, and `List.dedup` keeps last occurrences).
  Each entry of `V` is a name block above a `cl` separator.
* The edges are built on `Q` in reading order (`Q` is the reversed reading order) and moved to `O`
  at the end. Diamond `i` (the top entry of `V`) pushes its frame, its row (a `for` loop over `M`)
  and its detours: a walk of `F` onto `T` comparing every literal's name with the entry, with the
  clause's flags in the label, pushing the detour edges at each `cl`; `T` then goes back onto `F`.
  Vertex numbers are unary counters: `P` is the diamond top `hpT m i`, `N` is `hpR m i (3 m)`,
  `R` the current row vertex, `J` the clause, `D` the vertex `hpR m i (3 j + 1)`. A copy site
  (`Site`) pushes a counter in ones and then one or two constant bits.
* Finally the prefix `s`, `t`, `n = t + 1` is pushed onto `O` from `C` and `P`.

This file holds the machine, its quiescent states `MS` (counters in unary, `Q` as the list of
edge bits so far), the copy sites (`site_run`, `chain_run`), the name comparison with restore
(`cmpR_run`) and phase A (`phaseA_run`, ending at `h0` in the state `diaMS`). The diamonds, the
output and the emitter theorem `run` are in `HamPathEmit`. Phase A compares each new name with
every entry of `V`, so it is quadratic in `|toks φ|`.
-/

@[expose] public section

namespace Cslib.Complexity.Karp.EmitHam

open Turing Function MetaMathlibExt MetaMathlibExt.TM2Program Cslib.CookLevin Cslib.Logic.PL
  Computability Cslib.Complexity.SatVerifier
open Cslib.Complexity.SatVerifier.Lookup (isBitBlock_map isBitBlock_rev)

/-! ### The machine -/

/-- **Stacks of the HAMPATH emitter.** The emitter has eighteen distinct stacks: $T$ (the tokens),
$O$ (the output), $F$ (the tokens in reading order), $V$ (the distinct variables), $W$ (the other
side of the walk over $V$), $Q$ (the edges in progress), $G$ (garbage), $X$ and $Y$ (comparison
scratch), $C$ (the clause count), $M$ (three times the clause count), $P$ (the diamond top), $N$
(the row end), $R$ (the row vertex), $L$ (the row loop index), $J$ (the clause index), $D$ (the
detour vertex) and $Z$ (copy scratch). -/
inductive K | T | O | F | V | W | Q | G | X | Y | C | M | P | N | R | L | J | D | Z
  deriving DecidableEq

/-- The stacks, enumerated. -/
instance K.instFintypeEnumFix : Fintype K where
  elems := ⟨↑[K.T, .O, .F, .V, .W, .Q, .G, .X, .Y, .C, .M, .P, .N, .R, .L, .J, .D, .Z],
    by decide⟩
  complete := fun x => by cases x <;> decide

/-- **Stack alphabets of the HAMPATH emitter.** The alphabet of the output stack $O$ is the set of
bits (booleans); every other stack has the token symbols as its alphabet.

The counter stacks only ever hold the symbol $\mathrm{cl}$. -/
@[reducible] def Γ : K → Type
  | .O => Bool
  | _ => Sym

/-- **Counters read by HAMPATH copy sites.** The type with the five elements $p, n, r, j, d$, naming
the counters of the HAMPATH emitter that a copy site can read: the diamond top $p$, the row end
$n$, the row vertex $r$, the clause index $j$ and the detour vertex $d$. -/
inductive Src | p | n | r | j | d
  deriving DecidableEq

/-- **Stack of a HAMPATH copy-site counter.** The counters $p$, $n$, $r$, $j$, $d$ that a copy site
of the HAMPATH emitter reads are held on the emitter's stacks $P$, $N$, $R$, $J$, $D$ respectively
(the diamond top, the row end, the row vertex, the clause index and the detour vertex). -/
def Src.k : Src → K
  | .p => .P
  | .n => .N
  | .r => .R
  | .j => .J
  | .d => .D

/-- **Unit symbol of an emitter counter.** For every counter $s$ read by copy sites, the unit
symbol of $s$ is the token symbol $\mathrm{cl}$, as a letter of the alphabet of the stack that
holds $s$. -/
def Src.unit : (s : Src) → Γ s.k
  | .p => Sym.cl
  | .n => Sym.cl
  | .r => Sym.cl
  | .j => Sym.cl
  | .d => Sym.cl

/-- **Copy sites of the HAMPATH emitter.** The type of the twenty copy sites of the emitter
machine. Each site writes one endpoint of an edge of the emitted HAMPATH instance, $u$ for the
source and $v$ for the target: the sites $f_iu, f_iv$ for $i = 1, \dots, 4$ belong to the four
frame edges, $w_iu, w_iv$ for $i = 1, 2$ to the two row edges, and $d_iu, d_iv$ for
$i = 1, \dots, 4$ to the detour edges, positive for $i = 1, 2$ and negative for $i = 3, 4$. -/
inductive Site
  | f1u | f1v | f2u | f2v | f3u | f3v | f4u | f4v | w1u | w1v | w2u | w2v
  | d1u | d1v | d2u | d2v | d3u | d3v | d4u | d4v
  deriving DecidableEq

/-- **Copy sites of the HAMPATH emitter, listed.** The list of the twenty copy sites of the
HAMPATH emitter, in this order: the frame sites $f_1u, f_1v, f_2u, f_2v, f_3u, f_3v, f_4u, f_4v$,
the row sites $w_1u, w_1v, w_2u, w_2v$, and the detour sites
$d_1u, d_1v, d_2u, d_2v, d_3u, d_3v, d_4u, d_4v$. -/
def Site.all : List Site :=
  [.f1u, .f1v, .f2u, .f2v, .f3u, .f3v, .f4u, .f4v, .w1u, .w1v, .w2u, .w2v,
    .d1u, .d1v, .d2u, .d2v, .d3u, .d3v, .d4u, .d4v]

/-- The sites, enumerated. -/
instance Site.instFintypeEnumFix : Fintype Site :=
  Fintype.ofList Site.all (fun x => by cases x <;> decide)

/-- **Counter read by a copy site.** The map from copy sites to counters sending
$f_1u, f_1v, f_2u, f_3u$ to the diamond top $p$; $f_2v, f_3v, f_4u, f_4v$ to the row end $n$;
$w_1u, w_1v, w_2u, w_2v$ to the row vertex $r$; $d_1u, d_2v, d_3u, d_4v$ to the detour vertex
$d$; and $d_1v, d_2u, d_3v, d_4u$ to the clause index $j$. -/
def Site.src : Site → Src
  | .f1u | .f1v | .f2u | .f3u => .p
  | .f2v | .f3v | .f4u | .f4v => .n
  | .w1u | .w1v | .w2u | .w2v => .r
  | .d1u | .d2v | .d3u | .d4v => .d
  | .d1v | .d2u | .d3v | .d4u => .j

/-- **Extra ones of a copy site.** The number of extra ones a copy site adds to its counter's value
is $1$ for the sites $f_{1v}$, $f_{3u}$, $f_{3v}$, $f_{4v}$, $w_{1v}$, $w_{2u}$, $d_{2v}$ and
$d_{3u}$, and $0$ for every other site. -/
def Site.ext : Site → ℕ
  | .f1v | .f3u | .f3v | .f4v | .w1v | .w2u | .d2v | .d3u => 1
  | _ => 0

/-- **Labels of the HAMPATH emitter.** Let $f$, $p_p$, $p_n$ and $b$ range over bits and $j$ over
copy sites. A label of the emitter is one of $\mathrm{a0}$, $\mathrm{anm}$, $\mathrm{aw}(f)$,
$\mathrm{ac}(f)$, $\mathrm{ar1}(f)$, $\mathrm{ar2}(f)$, $\mathrm{amv}(f)$, $\mathrm{asep}(f)$,
$\mathrm{ab}(f)$, $\mathrm{ad2}$, $\mathrm{ad3}$, $\mathrm{b0}$, $\mathrm{b1}$,
$\mathrm{h0}, \dots, \mathrm{h5}$, $\mathrm{r0}, \dots, \mathrm{r4}$, $\mathrm{wi}$,
$\mathrm{e0}$, $\mathrm{e1}$, $\mathrm{e2}$, $\mathrm{dw}(p_p, p_n)$, $\mathrm{dk}(p_p, p_n)$,
$\mathrm{dr1}(p_p, p_n, b)$, $\mathrm{dr2}(p_p, p_n, b)$, $\mathrm{dm}(p_p, p_n, b)$,
$\mathrm{dl}(p_p, p_n, b)$, $\mathrm{dj}$, $\mathrm{t0}, \dots, \mathrm{t8}$,
$\mathrm{z0}, \dots, \mathrm{z9}$, $\mathrm{cpA}(j, b)$, $\mathrm{cpB}(j, b)$,
$\mathrm{post}(j, b)$ and $\mathrm{done}$, all distinct.

Their roles, in terms of the emitter's stacks: in phase A, $\mathrm{a0}$ reads a token,
$\mathrm{anm}$ moves a name to $F$, and $\mathrm{aw}(f)$ to $\mathrm{asep}(f)$ walk $V$, with $f$
recording whether a match was found ($\mathrm{ac}$ compares, $\mathrm{ar1}$ and $\mathrm{ar2}$
restore, $\mathrm{amv}$ and $\mathrm{asep}$ move the entry to $W$); $\mathrm{ab}(f)$ moves $W$ back
(and, when no match was found, pushes a separator), and $\mathrm{ad2}$, $\mathrm{ad3}$ copy the
name onto $V$. For the diamonds, $\mathrm{b0}$, $\mathrm{b1}$ set $P$; $\mathrm{h0}$ takes the next
entry; $\mathrm{h1}$ to $\mathrm{h5}$ set $N$; $\mathrm{r0}$ to $\mathrm{r4}$ run the row loop, with
$\mathrm{wi}$ advancing $R$; $\mathrm{e0}$ to $\mathrm{e2}$ set $D$; $\mathrm{dw}(p_p, p_n)$ walks
$F$ with the clause flags, $\mathrm{dk}$, $\mathrm{dr1}$, $\mathrm{dr2}$, $\mathrm{dm}$,
$\mathrm{dl}$ handle a literal with match bit $b$, and $\mathrm{dj}$ ends a clause; $\mathrm{t0}$
moves $T$ back to $F$, and $\mathrm{t1}$ to $\mathrm{t8}$ drop the entry and advance $P$. The labels
$\mathrm{z0}$ to $\mathrm{z9}$ produce the output, and $\mathrm{cpA}(j, b)$, $\mathrm{cpB}(j, b)$,
$\mathrm{post}(j, b)$ copy site $j$, passing $b$ on. -/
inductive Lab
  | a0 | anm | aw (f : Bool) | ac (f : Bool) | ar1 (f : Bool) | ar2 (f : Bool) | amv (f : Bool)
  | asep (f : Bool) | ab (f : Bool) | ad2 | ad3
  | b0 | b1 | h0 | h1 | h2 | h3 | h4 | h5 | r0 | r1 | r2 | r3 | r4 | wi | e0 | e1 | e2
  | dw (pp pn : Bool) | dk (pp pn : Bool) | dr1 (pp pn b : Bool) | dr2 (pp pn b : Bool)
  | dm (pp pn b : Bool) | dl (pp pn b : Bool) | dj
  | t0 | t1 | t2 | t3 | t4 | t5 | t6 | t7 | t8
  | z0 | z1 | z2 | z3 | z4 | z5 | z6 | z7 | z8 | z9
  | cpA (j : Site) (b : Bool) | cpB (j : Site) (b : Bool) | post (j : Site) (b : Bool) | done
  deriving DecidableEq

/-- **The four pairs of Booleans.** The list of all pairs of Booleans in the order
$(\mathrm{true}, \mathrm{true})$, $(\mathrm{true}, \mathrm{false})$,
$(\mathrm{false}, \mathrm{true})$, $(\mathrm{false}, \mathrm{false})$. -/
def bb : List (Bool × Bool) := [(true, true), (true, false), (false, true), (false, false)]

/-- The labels, enumerated. -/
instance Lab.instFintypeEnumFix : Fintype Lab :=
  Fintype.ofList
    ([Lab.a0, .anm, .ad2, .ad3, .b0, .b1, .h0, .h1, .h2, .h3, .h4, .h5, .r0, .r1, .r2, .r3,
        .r4, .wi, .e0, .e1, .e2, .dj, .t0, .t1, .t2, .t3, .t4, .t5, .t6, .t7, .t8, .z0, .z1,
        .z2, .z3, .z4, .z5, .z6, .z7, .z8, .z9, .done] ++
      ([true, false].flatMap fun f =>
        [Lab.aw f, .ac f, .ar1 f, .ar2 f, .amv f, .asep f, .ab f]) ++
      (bb.flatMap fun q => [Lab.dw q.1 q.2, .dk q.1 q.2]) ++
      (bb.flatMap fun q => [true, false].flatMap fun b =>
        [Lab.dr1 q.1 q.2 b, .dr2 q.1 q.2 b, .dm q.1 q.2 b, .dl q.1 q.2 b]) ++
      (Site.all.flatMap fun j => [true, false].flatMap fun b =>
        [Lab.cpA j b, .cpB j b, .post j b]))
    (fun x => by
      cases x <;> (try rename_i a b c; cases a <;> cases b <;> cases c) <;>
        (try rename_i a b; cases a <;> cases b) <;> (try rename_i a; cases a) <;> decide)

/-- **Label after a HAMPATH copy site.** For a copy site $j$ and a bit $b$, the label that follows
$j$ is $\mathrm{cpA}(j', b)$, where $j'$ is the site after $j$ in one of the chains
$f_{1u}, f_{1v}, f_{2u}, f_{2v}, f_{3u}, f_{3v}, f_{4u}, f_{4v}$, or
$w_{1u}, w_{1v}, w_{2u}, w_{2v}$, or $d_{1u}, d_{1v}, d_{2u}, d_{2v}$, or
$d_{3u}, d_{3v}, d_{4u}, d_{4v}$. At the ends of the chains it is $\mathrm{r0}$ after $f_{4v}$,
$\mathrm{wi}$ after $w_{2v}$ and $\mathrm{dj}$ after $d_{4v}$, whatever $b$ is; after $d_{2v}$ it
is $\mathrm{cpA}(d_{3u}, \mathrm{false})$ if $b$ is true and $\mathrm{dj}$ if $b$ is false. -/
def Site.nxt : Site → Bool → Lab
  | .f1u, b => .cpA .f1v b
  | .f1v, b => .cpA .f2u b
  | .f2u, b => .cpA .f2v b
  | .f2v, b => .cpA .f3u b
  | .f3u, b => .cpA .f3v b
  | .f3v, b => .cpA .f4u b
  | .f4u, b => .cpA .f4v b
  | .f4v, _ => .r0
  | .w1u, b => .cpA .w1v b
  | .w1v, b => .cpA .w2u b
  | .w2u, b => .cpA .w2v b
  | .w2v, _ => .wi
  | .d1u, b => .cpA .d1v b
  | .d1v, b => .cpA .d2u b
  | .d2u, b => .cpA .d2v b
  | .d2v, b => if b then .cpA .d3u false else .dj
  | .d3u, b => .cpA .d3v b
  | .d3v, b => .cpA .d4u b
  | .d4u, b => .cpA .d4v b
  | .d4v, _ => .dj

/-- **End of a clause in the detour walk.** For booleans $p_p$ and $p_n$ (the flags recording
whether the current clause contains the current variable positively, respectively negatively),
the detour walk continues at the end of the clause at the label where the first positive detour
site $d_{1u}$ starts with passed bit $p_n$ if $p_p$ is true; otherwise, if $p_n$ is true, at the
label where the first negative detour site $d_{3u}$ starts with passed bit false; and otherwise at
the label that ends the clause. -/
def clEnd (pp pn : Bool) : Lab := if pp then .cpA .d1u pn else if pn then .cpA .d3u false else .dj

/-- **The HAMPATH emitter machine.** The emitter is the multi-stack machine with the emitter's
stacks (the output stack $O$ holds bits, every other stack holds token symbols), the emitter's
labels, and a boolean internal state. Below, *moving the bit block* of a stack $A$ onto a stack
$B$ means popping $A$ while its top is a name bit $\mathrm{bit}(b)$ and pushing each popped bit
onto $B$ (as $\mathrm{bit}(b)$, or as the bit $b$ when $B = O$). *Comparing* $F$ with $V$ means
popping both while their tops are equal name bits, pushing each such bit onto $X$ and onto $Y$,
and ending with "equal" if both bit blocks end together and with "different", without popping,
at the first mismatch. *Draining* $A$, pushing on given stacks, means popping $A$ until it is
empty and pushing on each of those stacks one symbol per popped symbol. Every pushed symbol not
otherwise named is the separator $\mathrm{cl}$. A list of steps written for several labels in
turn is done one label at a time, each label passing to the next.

Phase A. At $\mathrm{a0}$: if $T$ is empty, go to $\mathrm{b0}$; if its top is $\mathrm{cl}$, pop
it, push $\mathrm{cl}$ once on $F$, once on $C$ and three times on $M$, and go to $\mathrm{a0}$;
otherwise pop it, push on $F$ the polarity marker $\mathrm{lit}(s)$, where $s$ is true exactly
when the popped symbol is $\mathrm{lit}(\mathrm{true})$, and go to $\mathrm{anm}$. At
$\mathrm{anm}$: move the bit block of $T$ onto $F$, then go to $\mathrm{aw}(\mathrm{false})$. At
$\mathrm{aw}(f)$: go to $\mathrm{ab}(f)$ if $V$ is empty and to $\mathrm{ac}(f)$ otherwise. At
$\mathrm{ac}(f)$: compare $F$ with $V$, then go to $\mathrm{ar1}(\mathrm{true})$ if equal and to
$\mathrm{ar1}(f)$ if different. At $\mathrm{ar1}(f)$, $\mathrm{ar2}(f)$, $\mathrm{amv}(f)$ in
turn: move the bit block of $X$ onto $F$, of $Y$ onto $V$, and of $V$ onto $W$, then go to
$\mathrm{asep}(f)$. At $\mathrm{asep}(f)$: pop $V$, push $\mathrm{cl}$ on $W$ and go to
$\mathrm{aw}(f)$. At $\mathrm{ab}(f)$: if $W$ is empty, go to $\mathrm{a0}$ if $f$ is true, and
otherwise push $\mathrm{cl}$ on $V$ and go to $\mathrm{ad2}$; if the top of $W$ is $\mathrm{cl}$,
pop it and push $\mathrm{cl}$ on $V$; otherwise pop it and push $\mathrm{bit}(s)$ on $V$, where
$s$ is true exactly when the popped symbol is $\mathrm{bit}(\mathrm{true})$; in these last two
cases go to $\mathrm{ab}(f)$. At $\mathrm{ad2}$: move the bit block of $F$ onto $X$ and go to
$\mathrm{ad3}$. At $\mathrm{ad3}$: if the top of $X$ is a name bit, pop it, push it on $F$ and on
$V$ and go to $\mathrm{ad3}$; otherwise go to $\mathrm{a0}$.

Diamonds. At $\mathrm{b0}$, $\mathrm{b1}$ in turn: drain $C$ pushing on $P$ and $Z$, then drain
$Z$ pushing on $C$, then go to $\mathrm{h0}$. At $\mathrm{h0}$: go to $\mathrm{z0}$ if $V$ is empty
and to $\mathrm{h1}$ otherwise. At $\mathrm{h1}, \dots, \mathrm{h5}$ in turn: drain $P$ pushing on
$N$ and $Z$, drain $Z$ pushing on $P$, drain $M$ pushing on $N$ and $Z$, drain $Z$ pushing on
$M$, and push $\mathrm{cl}$ on $N$, then go to $\mathrm{cpA}(f_{1u}, \mathrm{false})$. At
$\mathrm{r0}$, $\mathrm{r1}$, $\mathrm{r2}$ in turn: drain $P$ pushing on $R$ and $Z$, drain $Z$
pushing on $P$, and push $\mathrm{cl}$ on $R$, then go to $\mathrm{r3}$. At $\mathrm{r3}$: if $M$
is empty go to $\mathrm{r4}$, and otherwise pop it, push $\mathrm{cl}$ on $L$ and go to
$\mathrm{cpA}(w_{1u}, \mathrm{false})$. At $\mathrm{r4}$: drain $L$ pushing on $M$ and go to
$\mathrm{e0}$. At $\mathrm{wi}$: push $\mathrm{cl}$ on $R$ and go to $\mathrm{r3}$. At
$\mathrm{e0}$, $\mathrm{e1}$, $\mathrm{e2}$ in turn: drain $P$ pushing on $D$ and $Z$, drain $Z$
pushing on $P$, and push $\mathrm{cl}$ twice on $D$, then go to
$\mathrm{dw}(\mathrm{false}, \mathrm{false})$.

Detours. At $\mathrm{dw}(p_p, p_n)$: if $F$ is empty go to $\mathrm{t0}$; if its top is
$\mathrm{cl}$, go to $\mathrm{cpA}(d_{1u}, p_n)$ if $p_p$ is true, else to
$\mathrm{cpA}(d_{3u}, \mathrm{false})$ if $p_n$ is true, else to $\mathrm{dj}$; otherwise go to
$\mathrm{dk}(p_p, p_n)$. At $\mathrm{dk}(p_p, p_n)$: compare $F$ with $V$, then go to
$\mathrm{dr1}(p_p, p_n, \mathrm{true})$ if equal and to $\mathrm{dr1}(p_p, p_n, \mathrm{false})$
if different. At $\mathrm{dr1}$, $\mathrm{dr2}$, $\mathrm{dm}$ with parameters $(p_p, p_n, b)$ in
turn: move the bit block of $X$ onto $F$, of $Y$ onto $V$, and of $F$ onto $T$, then go to
$\mathrm{dl}(p_p, p_n, b)$. At $\mathrm{dl}(p_p, p_n, b)$: pop $F$, push $\mathrm{lit}(s)$ on $T$,
where $s$ is true exactly when the popped symbol is $\mathrm{lit}(\mathrm{true})$, and go to
$\mathrm{dw}(p_p \lor (b \land s), p_n \lor (b \land \lnot s))$. At $\mathrm{dj}$: pop $F$, push
$\mathrm{cl}$ once on $T$, once on $J$ and three times on $D$, and go to
$\mathrm{dw}(\mathrm{false}, \mathrm{false})$. At $\mathrm{t0}$: if $T$ is empty go to
$\mathrm{t1}$; otherwise pop it, push on $F$ the symbol $\mathrm{cl}$ if the popped symbol is
$\mathrm{cl}$, $\mathrm{bit}(b)$ if it is $\mathrm{bit}(b)$, and otherwise $\mathrm{lit}(s)$ with
$s$ true exactly when it is $\mathrm{lit}(\mathrm{true})$, and go to $\mathrm{t0}$. At
$\mathrm{t1}, \dots, \mathrm{t8}$ in turn: move the bit block of $V$ onto $G$, pop $V$, drain $P$
pushing nothing, drain $N$ pushing on $P$, push $\mathrm{cl}$ on $P$, and drain $R$, $J$ and $D$
pushing nothing, then go to $\mathrm{h0}$.

Output. At $\mathrm{z0}$: move the bit block of $Q$ onto $O$ and go to $\mathrm{z1}$. At
$\mathrm{z1}, \dots, \mathrm{z9}$ in turn: push false and then true on $O$; drain $P$ pushing
true on $O$ and $\mathrm{cl}$ on $Z$; drain $Z$ pushing on $P$; push false on $O$; drain $P$
pushing true on $O$ and $\mathrm{cl}$ on $Z$; drain $Z$ pushing on $P$; push false on $O$; drain
$C$ pushing true on $O$ and $\mathrm{cl}$ on $Z$; and drain $Z$ pushing on $C$; then go to
$\mathrm{done}$. At $\mathrm{done}$: halt.

Copy sites. For a copy site $j$ and a bit $b$: at $\mathrm{cpA}(j, b)$, drain the stack of the
counter that $j$ reads, pushing $\mathrm{bit}(\mathrm{true})$ on $Q$ and $\mathrm{cl}$ on $Z$, and
go to $\mathrm{cpB}(j, b)$; at $\mathrm{cpB}(j, b)$, drain $Z$ pushing $\mathrm{cl}$ on the stack
of the counter that $j$ reads, and go to $\mathrm{post}(j, b)$; at $\mathrm{post}(j, b)$, in one
step push on $Q$ one $\mathrm{bit}(\mathrm{true})$ for each of the ones that $j$ adds to its
counter and then $\mathrm{bit}(\mathrm{false})$, and go to the label that follows $j$ for $b$. -/
def prog : Lab → TM2.Stmt Γ Lab Bool
  | .a0 => .peek .T (fun _ o => o.isNone) <| .branch id (.goto fun _ => .b0) <|
      .peek .T (fun _ o => o == some .cl) <| .branch id
        (.pop .T (fun s _ => s) <| .push .F (fun _ => Sym.cl) <| .push .C (fun _ => Sym.cl) <|
          pushList .M [Sym.cl, Sym.cl, Sym.cl] <| .goto fun _ => .a0)
        (.pop .T (fun _ o => o == some (.lit true)) <| .push .F (fun s => Sym.lit s) <|
          .goto fun _ => .anm)
  | .anm => moveB .T .F Sym.bit? Sym.bit .anm (.aw false)
  | .aw f => .peek .V (fun _ o => o.isNone) <| .branch id (.goto fun _ => .ab f)
      (.goto fun _ => .ac f)
  | .ac f => cmpB .F .V .X .Y Sym.bit? Sym.bit? Sym.bit Sym.bit (.ac f) (.ar1 true) (.ar1 f)
  | .ar1 f => moveB .X .F Sym.bit? Sym.bit (.ar1 f) (.ar2 f)
  | .ar2 f => moveB .Y .V Sym.bit? Sym.bit (.ar2 f) (.amv f)
  | .amv f => moveB .V .W Sym.bit? Sym.bit (.amv f) (.asep f)
  | .asep f => .pop .V (fun s _ => s) <| .push .W (fun _ => Sym.cl) <| .goto fun _ => .aw f
  | .ab f => .peek .W (fun _ o => o.isNone) <| .branch id
      (if f then .goto fun _ => .a0 else .push .V (fun _ => Sym.cl) <| .goto fun _ => .ad2) <|
      .peek .W (fun _ o => o == some .cl) <| .branch id
        (.pop .W (fun s _ => s) <| .push .V (fun _ => Sym.cl) <| .goto fun _ => .ab f)
        (.pop .W (fun _ o => o == some (.bit true)) <| .push .V (fun s => Sym.bit s) <|
          .goto fun _ => .ab f)
  | .ad2 => moveB .F .X Sym.bit? Sym.bit .ad2 .ad3
  | .ad3 => .peek .X (fun _ o => isBit Sym.bit? o) <| .branch id
      (.pop .X (fun _ o => bitOf Sym.bit? o) <| .push .F (fun s => Sym.bit s) <|
        .push .V (fun s => Sym.bit s) <| .goto fun _ => .ad3)
      (.goto fun _ => .a0)
  | .b0 => xfer .C [⟨.P, Sym.cl⟩, ⟨.Z, Sym.cl⟩] .b0 .b1
  | .b1 => xfer .Z [⟨.C, Sym.cl⟩] .b1 .h0
  | .h0 => .peek .V (fun _ o => o.isNone) <| .branch id (.goto fun _ => .z0)
      (.goto fun _ => .h1)
  | .h1 => xfer .P [⟨.N, Sym.cl⟩, ⟨.Z, Sym.cl⟩] .h1 .h2
  | .h2 => xfer .Z [⟨.P, Sym.cl⟩] .h2 .h3
  | .h3 => xfer .M [⟨.N, Sym.cl⟩, ⟨.Z, Sym.cl⟩] .h3 .h4
  | .h4 => xfer .Z [⟨.M, Sym.cl⟩] .h4 .h5
  | .h5 => .push .N (fun _ => Sym.cl) <| .goto fun _ => .cpA .f1u false
  | .r0 => xfer .P [⟨.R, Sym.cl⟩, ⟨.Z, Sym.cl⟩] .r0 .r1
  | .r1 => xfer .Z [⟨.P, Sym.cl⟩] .r1 .r2
  | .r2 => .push .R (fun _ => Sym.cl) <| .goto fun _ => .r3
  | .r3 => forHead .M .L Sym.cl (.cpA .w1u false) .r4
  | .r4 => xfer .L [⟨.M, Sym.cl⟩] .r4 .e0
  | .wi => .push .R (fun _ => Sym.cl) <| .goto fun _ => .r3
  | .e0 => xfer .P [⟨.D, Sym.cl⟩, ⟨.Z, Sym.cl⟩] .e0 .e1
  | .e1 => xfer .Z [⟨.P, Sym.cl⟩] .e1 .e2
  | .e2 => pushList .D [Sym.cl, Sym.cl] <| .goto fun _ => .dw false false
  | .dw pp pn => .peek .F (fun _ o => o.isNone) <| .branch id (.goto fun _ => .t0) <|
      .peek .F (fun _ o => o == some .cl) <| .branch id
        (.goto fun _ => clEnd pp pn) (.goto fun _ => .dk pp pn)
  | .dk pp pn => cmpB .F .V .X .Y Sym.bit? Sym.bit? Sym.bit Sym.bit (.dk pp pn)
      (.dr1 pp pn true) (.dr1 pp pn false)
  | .dr1 pp pn b => moveB .X .F Sym.bit? Sym.bit (.dr1 pp pn b) (.dr2 pp pn b)
  | .dr2 pp pn b => moveB .Y .V Sym.bit? Sym.bit (.dr2 pp pn b) (.dm pp pn b)
  | .dm pp pn b => moveB .F .T Sym.bit? Sym.bit (.dm pp pn b) (.dl pp pn b)
  | .dl pp pn b => .pop .F (fun _ o => o == some (.lit true)) <|
      .push .T (fun s => Sym.lit s) <| .goto fun s => .dw (pp || (b && s)) (pn || (b && !s))
  | .dj => .pop .F (fun s _ => s) <| .push .T (fun _ => Sym.cl) <|
      .push .J (fun _ => Sym.cl) <| pushList .D [Sym.cl, Sym.cl, Sym.cl] <|
        .goto fun _ => .dw false false
  | .t0 => .peek .T (fun _ o => o.isNone) <| .branch id (.goto fun _ => .t1) <|
      .peek .T (fun _ o => o == some .cl) <| .branch id
        (.pop .T (fun s _ => s) <| .push .F (fun _ => Sym.cl) <| .goto fun _ => .t0) <|
      .peek .T (fun _ o => isBit Sym.bit? o) <| .branch id
        (.pop .T (fun _ o => bitOf Sym.bit? o) <| .push .F (fun s => Sym.bit s) <|
          .goto fun _ => .t0)
        (.pop .T (fun _ o => o == some (.lit true)) <| .push .F (fun s => Sym.lit s) <|
          .goto fun _ => .t0)
  | .t1 => moveB .V .G Sym.bit? Sym.bit .t1 .t2
  | .t2 => .pop .V (fun s _ => s) <| .goto fun _ => .t3
  | .t3 => xfer .P [] .t3 .t4
  | .t4 => xfer .N [⟨.P, Sym.cl⟩] .t4 .t5
  | .t5 => .push .P (fun _ => Sym.cl) <| .goto fun _ => .t6
  | .t6 => xfer .R [] .t6 .t7
  | .t7 => xfer .J [] .t7 .t8
  | .t8 => xfer .D [] .t8 .h0
  | .z0 => moveB .Q .O Sym.bit? id .z0 .z1
  | .z1 => pushList .O [false, true] <| .goto fun _ => .z2
  | .z2 => xfer .P [⟨.O, true⟩, ⟨.Z, Sym.cl⟩] .z2 .z3
  | .z3 => xfer .Z [⟨.P, Sym.cl⟩] .z3 .z4
  | .z4 => .push .O (fun _ => false) <| .goto fun _ => .z5
  | .z5 => xfer .P [⟨.O, true⟩, ⟨.Z, Sym.cl⟩] .z5 .z6
  | .z6 => xfer .Z [⟨.P, Sym.cl⟩] .z6 .z7
  | .z7 => .push .O (fun _ => false) <| .goto fun _ => .z8
  | .z8 => xfer .C [⟨.O, true⟩, ⟨.Z, Sym.cl⟩] .z8 .z9
  | .z9 => xfer .Z [⟨.C, Sym.cl⟩] .z9 .done
  | .cpA j b => xfer j.src.k [⟨.Q, Sym.bit true⟩, ⟨.Z, Sym.cl⟩] (.cpA j b) (.cpB j b)
  | .cpB j b => xfer .Z [⟨j.src.k, j.src.unit⟩] (.cpB j b) (.post j b)
  | .post j b => emit .Q ((List.replicate j.ext true ++ [false]).map Sym.bit) (j.nxt b)
  | .done => .halt

/-- **Start label of the HAMPATH emitter.** The emitter machine starts at the label $a_0$, the
first phase A label, which reads the next token. -/
def start : Lab := .a0

/-! ### Quiescent states -/

/-- **Quiescent states of the HAMPATH emitter.** A quiescent state consists of lists of token
symbols $t$, $f$, $v$, $w$, $g$, $x$ (meant as the token stack, the tokens in reading order, the
distinct variables, the other side of the variable walk, garbage, and the first comparison
scratch stack), a list of bits $o$ (the output stack), a list of bits $q$ (the edge bits so far,
in reading order), and natural numbers $c$, $c_3$, $p$, $n$, $r$, $l$, $j$, $d$ (meant as the
clause count, three times it, the diamond top, the row end, the row vertex, the row loop index,
the clause index and the detour vertex).

On the emitter's stacks such a state holds each counter as a unary stack of $\mathrm{cl}$ symbols
and the edge bits $q$ on $Q$ reversed, as name-bit symbols; the scratch stacks $Y$ and $Z$ are
empty, and $X$ is empty except while a new name is copied onto $V$. -/
structure MS where
  /-- The token stack. -/
  t : List Sym
  /-- The output stack. -/
  o : List Bool
  /-- The tokens in reading order. -/
  f : List Sym
  /-- The distinct variables. -/
  v : List Sym
  /-- The variable walk's other side. -/
  w : List Sym
  /-- The edge bits so far, in reading order. -/
  q : List Bool
  /-- Garbage. -/
  g : List Sym
  /-- The first comparison scratch stack. -/
  x : List Sym
  /-- The clause count. -/
  c : ℕ
  /-- Three times the clause count. -/
  mm : ℕ
  /-- The diamond top. -/
  p : ℕ
  /-- The row end. -/
  n : ℕ
  /-- The row vertex. -/
  r : ℕ
  /-- The row loop index. -/
  l : ℕ
  /-- The clause index. -/
  j : ℕ
  /-- The detour vertex. -/
  d : ℕ

/-- **Stacks of a quiescent emitter state.** In a quiescent state $s$, the stacks $T$, $O$, $F$,
$V$, $W$, $G$ and $X$ hold the lists that $s$ records for them; the stack $Q$ holds the edge
bits of $s$ as bit symbols, reversed so that the last bit is on top; each counter stack $C$,
$M$, $P$, $N$, $R$, $L$, $J$, $D$ holds as many copies of the symbol $\mathrm{cl}$ as the
value that $s$ records for the corresponding counter (the clause count, the counter reserved
for three times the clause count, the diamond top, the row end, the row vertex, the row loop
index, the clause index and the detour vertex), with no relation imposed between these values;
and the scratch stacks $Y$ and $Z$ are empty. -/
def MS.stk (s : MS) : ∀ k, List (Γ k)
  | .T => s.t
  | .O => s.o
  | .F => s.f
  | .V => s.v
  | .W => s.w
  | .Q => s.q.reverse.map Sym.bit
  | .G => s.g
  | .C => cnt Sym.cl s.c
  | .M => cnt Sym.cl s.mm
  | .P => cnt Sym.cl s.p
  | .N => cnt Sym.cl s.n
  | .R => cnt Sym.cl s.r
  | .L => cnt Sym.cl s.l
  | .J => cnt Sym.cl s.j
  | .D => cnt Sym.cl s.d
  | .X => s.x
  | .Y | .Z => []

/-- **Counter values of a quiescent emitter state.** For a quiescent state $s$, the value of the
counters $p$, $n$, $r$, $j$, $d$ is respectively the diamond top, the row end, the row vertex,
the clause index and the detour vertex recorded in $s$. -/
def MS.val (s : MS) : Src → ℕ
  | .p => s.p
  | .n => s.n
  | .r => s.r
  | .j => s.j
  | .d => s.d

section MSLemmas

variable (s : MS)

@[simp] theorem stk_T : s.stk .T = s.t := rfl
@[simp] theorem stk_O : s.stk .O = s.o := rfl
@[simp] theorem stk_F : s.stk .F = s.f := rfl
@[simp] theorem stk_V : s.stk .V = s.v := rfl
@[simp] theorem stk_W : s.stk .W = s.w := rfl
@[simp] theorem stk_Q : s.stk .Q = s.q.reverse.map Sym.bit := rfl
@[simp] theorem stk_G : s.stk .G = s.g := rfl
@[simp] theorem stk_C : s.stk .C = List.replicate s.c Sym.cl := rfl
@[simp] theorem stk_M : s.stk .M = List.replicate s.mm Sym.cl := rfl
@[simp] theorem stk_P : s.stk .P = List.replicate s.p Sym.cl := rfl
@[simp] theorem stk_N : s.stk .N = List.replicate s.n Sym.cl := rfl
@[simp] theorem stk_R : s.stk .R = List.replicate s.r Sym.cl := rfl
@[simp] theorem stk_L : s.stk .L = List.replicate s.l Sym.cl := rfl
@[simp] theorem stk_J : s.stk .J = List.replicate s.j Sym.cl := rfl
@[simp] theorem stk_D : s.stk .D = List.replicate s.d Sym.cl := rfl
@[simp] theorem stk_X : s.stk .X = s.x := rfl
@[simp] theorem stk_Y : s.stk .Y = [] := rfl
@[simp] theorem stk_Z : s.stk .Z = [] := rfl

@[simp] theorem upd_T (x : List Sym) : update s.stk .T x = {s with t := x}.stk := by
  funext k; cases k <;> rfl
@[simp] theorem upd_O (x : List Bool) : update s.stk .O x = {s with o := x}.stk := by
  funext k; cases k <;> rfl
@[simp] theorem upd_F (x : List Sym) : update s.stk .F x = {s with f := x}.stk := by
  funext k; cases k <;> rfl
@[simp] theorem upd_V (x : List Sym) : update s.stk .V x = {s with v := x}.stk := by
  funext k; cases k <;> rfl
@[simp] theorem upd_W (x : List Sym) : update s.stk .W x = {s with w := x}.stk := by
  funext k; cases k <;> rfl
@[simp] theorem upd_G (x : List Sym) : update s.stk .G x = {s with g := x}.stk := by
  funext k; cases k <;> rfl
@[simp] theorem upd_X (y : List Sym) : update s.stk .X y = {s with x := y}.stk := by
  funext k; cases k <;> rfl
theorem upd_Q (q : List Bool) :
    update s.stk .Q (q.reverse.map Sym.bit) = {s with q := q}.stk := by
  funext k; cases k <;> rfl
theorem upd_C (x : ℕ) : update s.stk .C (cnt Sym.cl x) = {s with c := x}.stk := by
  funext k; cases k <;> rfl
theorem upd_M (x : ℕ) : update s.stk .M (cnt Sym.cl x) = {s with mm := x}.stk := by
  funext k; cases k <;> rfl
theorem upd_P (x : ℕ) : update s.stk .P (cnt Sym.cl x) = {s with p := x}.stk := by
  funext k; cases k <;> rfl
theorem upd_N (x : ℕ) : update s.stk .N (cnt Sym.cl x) = {s with n := x}.stk := by
  funext k; cases k <;> rfl
theorem upd_R (x : ℕ) : update s.stk .R (cnt Sym.cl x) = {s with r := x}.stk := by
  funext k; cases k <;> rfl
theorem upd_L (x : ℕ) : update s.stk .L (cnt Sym.cl x) = {s with l := x}.stk := by
  funext k; cases k <;> rfl
theorem upd_J (x : ℕ) : update s.stk .J (cnt Sym.cl x) = {s with j := x}.stk := by
  funext k; cases k <;> rfl
theorem upd_D (x : ℕ) : update s.stk .D (cnt Sym.cl x) = {s with d := x}.stk := by
  funext k; cases k <;> rfl

theorem stk_src (u : Src) : s.stk u.k = cnt u.unit (s.val u) := by cases u <;> rfl

end MSLemmas

@[simp] theorem sym_beq (a b : Sym) : (a == b) = decide (a = b) := rfl

theorem runLe_cast {k k' : ℕ} {c d d' : TM2.Cfg Γ Lab Bool} (h : RunLe prog k c d)
    (hk : k ≤ k') (hd : d = d') : RunLe prog k' c d' := hd ▸ h.mono hk

/-! ### Copies and copy sites -/

/-- **Copying a counter in the HAMPATH emitter.** Let $a$, $c$ and $Z$ be three distinct stacks of
the emitter machine (with $Z$ its copy scratch stack), $u$ a symbol of $a$ and $x$ a symbol of $c$.
Suppose the machine at label $l_1$ pops $a$ until it is empty, pushing $x$ onto $c$ and the
clause separator $\mathrm{cl}$ onto $Z$ for each popped symbol, and then continues at $l_2$; and
at $l_2$ pops $Z$ until it is empty, pushing $u$ onto $a$ for each popped symbol, and then
continues at $l'$. If the stacks $S$ hold exactly $n$ copies of $u$ on $a$ and nothing on $Z$,
then for every flag $v$ there is a flag $v'$ such that the machine goes in exactly $2n + 2$ steps
from label $l_1$ with flag $v$ and stacks $S$ to label $l'$ with flag $v'$ and the stacks $S$
with $n$ copies of $x$ pushed onto $c$. -/
theorem cp_run {a c : K} (ua : Γ a) (x : Γ c) (hca : c ≠ a) (haZ : a ≠ .Z) (hcZ : c ≠ .Z)
    {l₁ l₂ next : Lab} (h₁ : prog l₁ = xfer a [⟨c, x⟩, ⟨.Z, Sym.cl⟩] l₁ l₂)
    (h₂ : prog l₂ = xfer .Z [⟨a, ua⟩] l₂ next) (val : ℕ) (v : Bool) (S : ∀ k, List (Γ k))
    (hS : S a = cnt ua val) (hZ : S .Z = []) :
    ∃ v', Run prog (2 * val + 2) ⟨some l₁, v, S⟩
      ⟨some next, v', update S c (cnt x val ++ S c)⟩ := by
  have r₁ := xfer_run h₁ (pair_nodupKeys x (Sym.cl : Γ .Z) hcZ) (by simp [hca.symm, haZ]) ua
    val v S hS
  set S₁ := addU [⟨c, x⟩, ⟨.Z, Sym.cl⟩] val (update S a []) with hS₁
  have h₁Z : S₁ .Z = cnt (Sym.cl : Γ .Z) val := by
    rw [hS₁, addU_pair_snd _ _ _ _ hcZ.symm, update_of_ne haZ.symm, hZ, List.append_nil]
  have r₂ := xfer_run h₂ (single_nodupKeys ua) (by simp [haZ.symm]) (Sym.cl : Γ .Z) val
    (Flag.tag false) S₁ h₁Z
  have hfin : addU [⟨a, ua⟩] val (update S₁ .Z []) = update S c (cnt x val ++ S c) := by
    funext k
    by_cases hka : k = a
    · subst hka
      rw [addU_single_self, update_of_ne haZ, hS₁, addU_pair_ne _ _ _ _ hca.symm haZ,
        update_self, update_of_ne hca.symm, hS, List.append_nil]
    rw [addU_single_ne _ _ _ hka]
    by_cases hkZ : k = .Z
    · subst hkZ; rw [update_self, update_of_ne hcZ.symm, hZ]
    rw [update_of_ne hkZ]
    by_cases hkc : k = c
    · subst hkc; rw [hS₁, addU_pair_fst, update_of_ne hca, update_self]
    rw [hS₁, addU_pair_ne _ _ _ _ hkc hkZ, update_of_ne hka, update_of_ne hkc]
  rw [hfin] at r₂
  exact ⟨_, (r₁.trans r₂).of_eq (by omega)⟩

theorem Src.k_ne_Q (u : Src) : u.k ≠ .Q := by cases u <;> decide

theorem Src.k_ne_Z (u : Src) : u.k ≠ .Z := by cases u <;> decide

/-- **Bits pushed by a copy site of the HAMPATH emitter.** For a quiescent state $s$ of the
HAMPATH emitter and a copy site $j$, the atom of $j$ in $s$ is the list of $c + e$ copies of
true followed by one false, where $c$ is the value in $s$ of the counter that $j$ copies and
$e \in \{0, 1\}$ is the number of extra ones that $j$ adds. -/
def atom (s : MS) (j : Site) : List Bool := List.replicate (s.val j.src + j.ext) true ++ [false]

theorem q_push (q x : List Bool) (e : ℕ) :
    ((List.replicate e true ++ [false]).map Sym.bit).reverse ++
      (cnt (Sym.bit true) x.length ++ q.reverse.map Sym.bit) =
      (q ++ (List.replicate (x.length + e) true ++ [false])).reverse.map Sym.bit := by
  rw [Nat.add_comm]
  simp [List.map_reverse, List.reverse_append, cnt, ← List.append_assoc]

/-- **Run of a HAMPATH copy site.** Let $j$ be a copy site, $b$ and $v$ bits and $s$ a quiescent
state of the HAMPATH emitter; let $c$ be the value in $s$ of the counter that $j$ reads and $e$
the number of ones that $j$ adds to its counter. Started at label $\mathrm{cpA}(j, b)$ with
internal state $v$ and the stacks of $s$, the emitter runs in exactly $2c + 3$ steps to the label
that follows $j$ for $b$, with some internal state and the stacks of the quiescent state obtained
from $s$ by appending $c + e$ copies of true followed by one false to its edge bits. -/
theorem site_run (j : Site) (b : Bool) (s : MS) (v : Bool) :
    ∃ v', Run prog (2 * s.val j.src + 3) ⟨some (.cpA j b), v, s.stk⟩
      ⟨some (j.nxt b), v', {s with q := s.q ++ atom s j}.stk⟩ := by
  obtain ⟨v₁, r₁⟩ := cp_run (a := j.src.k) (c := .Q) j.src.unit (Sym.bit true)
    (Ne.symm j.src.k_ne_Q) j.src.k_ne_Z (by decide) (l₁ := .cpA j b) (l₂ := .cpB j b)
    (next := .post j b) rfl rfl (s.val j.src) v s.stk (stk_src s j.src) rfl
  have r₂ := emit_run (M := prog) (self := .post j b) (next := j.nxt b) (k := .Q)
    (xs := (List.replicate j.ext true ++ [false]).map Sym.bit) rfl v₁
    (update s.stk .Q (cnt (Sym.bit true) (s.val j.src) ++ s.stk .Q))
  have e : update (update s.stk .Q (cnt (Sym.bit true) (s.val j.src) ++ s.stk .Q)) .Q
      (((List.replicate j.ext true ++ [false]).map Sym.bit).reverse ++
        update s.stk .Q (cnt (Sym.bit true) (s.val j.src) ++ s.stk .Q) .Q) =
      {s with q := s.q ++ atom s j}.stk := by
    rw [update_idem, update_self, stk_Q]
    have := q_push s.q (List.replicate (s.val j.src) true) j.ext
    rw [List.length_replicate] at this
    rw [this, upd_Q]
    rfl
  rw [e] at r₂
  exact ⟨v₁, (r₁.trans r₂).of_eq (by omega)⟩

/-- **Copy sites chained in the HAMPATH emitter.** Copy sites $j_1, \dots, j_n$ are chained from
label $l_0$ to label $l$ with passed bit $b$ when $l_0$ is the label at which $j_1$ starts with
passed bit $b$, the label where each $j_i$ with $i < n$ continues with passed bit $b$ is the label
at which $j_{i+1}$ starts with passed bit $b$, and $j_n$ continues at $l$ with passed bit $b$. The
empty list of sites is chained from $l_0$ to $l$ exactly when $l_0 = l$. -/
def Chain : List Site → Bool → Lab → Lab → Bool
  | [], _, l₀, l => l₀ == l
  | j :: js, b, l₀, l => l₀ == .cpA j b && Chain js b (j.nxt b) l

/-- **Step count of a list of copy sites in the HAMPATH emitter.** For a quiescent state $s$ and
copy sites $j_1, \dots, j_n$, the step count is $\sum_{i=1}^{n} (2 v_i + 3)$, where $v_i$ is the
value in $s$ of the counter that $j_i$ copies. -/
def chainCost (s : MS) (js : List Site) : ℕ := (js.map fun j => 2 * s.val j.src + 3).sum

theorem atom_q (s : MS) (x : List Bool) : atom {s with q := x} = atom s := by
  funext j'; simp only [atom]; cases j'.src <;> rfl

theorem chainCost_q (s : MS) (x : List Bool) (js : List Site) :
    chainCost {s with q := x} js = chainCost s js := by
  simp only [chainCost]; congr 1

theorem chainCost_le (s : MS) (Bd : ℕ) (hB : ∀ u, s.val u ≤ Bd) (js : List Site) :
    chainCost s js ≤ js.length * (2 * Bd + 3) := by
  induction js with
  | nil => simp [chainCost]
  | cons j js ih =>
      have := hB j.src
      simp only [chainCost, List.map_cons, List.sum_cons, List.length_cons] at ih ⊢
      nlinarith

/-- **Running a chain of copy sites in the HAMPATH emitter.** Let $j_1, \dots, j_n$ be copy sites
chained from label $l_0$ to label $l$ with passed bit $b$. Then for every quiescent state $s$ and
every flag $v$ there is a flag $v'$ such that the emitter machine goes, in exactly as many steps as
the step count of $j_1, \dots, j_n$ at $s$, from label $l_0$ with flag $v$ and the stacks of $s$ to
label $l$ with flag $v'$ and the stacks of the state that differs from $s$ only in that the atoms
of $j_1, \dots, j_n$ at $s$, concatenated in this order, are appended to its edge bits. -/
theorem chain_run (js : List Site) : ∀ (s : MS) (b : Bool) (l₀ l : Lab),
    Chain js b l₀ l = true → ∀ v : Bool, ∃ v', Run prog (chainCost s js) ⟨some l₀, v, s.stk⟩
      ⟨some l, v', {s with q := s.q ++ (js.map (atom s)).flatten}.stk⟩ := by
  induction js with
  | nil =>
      intro s b l₀ l h v
      simp only [Chain, beq_iff_eq] at h
      subst h
      exact ⟨v, by simpa [chainCost] using Run.zero (M := prog) _⟩
  | cons j js ih =>
      intro s b l₀ l h v
      simp only [Chain, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨rfl, h⟩ := h
      obtain ⟨v₁, r₁⟩ := site_run j b s v
      obtain ⟨v₂, r₂⟩ := ih {s with q := s.q ++ atom s j} b (j.nxt b) l h v₁
      rw [chainCost_q] at r₂
      have e : chainCost s (j :: js) = 2 * s.val j.src + 3 + chainCost s js := by
        simp [chainCost]
      rw [e]
      have r := r₁.trans r₂
      simp only [atom_q, List.append_assoc] at r
      exact ⟨v₂, by simpa using r⟩

/-! ### Comparing a name on `F` with the top entry of `V` -/

/-- **A symbol that reads as a name bit is that bit.** For every symbol $x$ of the stack alphabet
of the SAT verifier and every bit $b$, if $x$ reads as the name bit $b$, then $x$ is the name-bit
symbol for $b$. -/
theorem bit_inv (x : Sym) (b : Bool) (h : Sym.bit? x = some b) : Sym.bit b = x := by
  cases x <;> simp_all [Sym.bit?]

/-- **Comparing a name with the top entry of the variable stack.** Let $l_c$ be a label at which
the emitter machine compares the bit blocks of the stacks $F$ and $V$, with scratch stacks $X$ and
$Y$, going to $r_1(b_T)$ if the blocks are equal and to $r_1(b_F)$ otherwise. Suppose that for each
bit $b$ the machine at $r_1(b)$ moves the bit block of $X$ onto $F$ and then continues at
$r_2(b)$, and at $r_2(b)$ moves the bit block of $Y$ onto $V$ and then continues at $n_x(b)$. Let
$s$ be a quiescent state whose stack $F$ holds the bit symbols of a bit list $u$ followed by a list
$A$, whose stack $V$ holds the bit symbols of a bit list $w$ followed by a list $B$, where neither
$A$ nor $B$ starts with a bit symbol, and whose stack $X$ is empty. Then for every flag $v$ there is
a flag $v'$ such that the machine goes in at most $3 |w| + 3$ steps from label $l_c$ with flag $v$
and the stacks of $s$ to label $n_x(b_T)$ if $u = w$ and to $n_x(b_F)$ otherwise, with flag $v'$
and again the stacks of $s$. -/
theorem cmpR_run {lc : Lab} {r1 r2 nx : Bool → Lab} {bT bF : Bool}
    (hc : prog lc = cmpB .F .V .X .Y Sym.bit? Sym.bit? Sym.bit Sym.bit lc (r1 bT) (r1 bF))
    (h1 : ∀ b, prog (r1 b) = moveB .X .F Sym.bit? Sym.bit (r1 b) (r2 b))
    (h2 : ∀ b, prog (r2 b) = moveB .Y .V Sym.bit? Sym.bit (r2 b) (nx b))
    (s : MS) (v : Bool) (u w : List Bool) (A B : List Sym) (hA : A.head?.bind Sym.bit? = none)
    (hB : B.head?.bind Sym.bit? = none) (hf : s.f = u.map Sym.bit ++ A)
    (hv : s.v = w.map Sym.bit ++ B) (hx : s.x = []) :
    ∃ v', RunLe prog (3 * w.length + 3) ⟨some lc, v, s.stk⟩
      ⟨some (nx (if u = w then bT else bF)), v', s.stk⟩ := by
  have hd : Distinct4 K.F K.V K.X K.Y :=
    ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
  obtain ⟨cp, v₁, S₁, hcu, hcw, -, r₁, h1F, h1V, h1X, h1Y, h1k⟩ := cmpB_run (M := prog)
    (self := lc) (eqL := r1 bT) (neL := r1 bF) (a := .F) (b := .V)
    (ta := .X) (tb := .Y) (da := Sym.bit?) (db := Sym.bit?) (ea := Sym.bit) (eb := Sym.bit) hc
    hd u w (u.map Sym.bit) A (w.map Sym.bit) B v s.stk (by simp [hf]) (by simp [hv])
    (isBitBlock_map u) (isBitBlock_map w) hA hB
  set b := if u = w then bT else bF with hb
  have hl : (if u = w then r1 bT else r1 bF) = r1 b := by rw [hb]; split <;> rfl
  rw [hl] at r₁
  obtain ⟨v₂, S₂, r₂, h2X, h2F, h2k⟩ := moveB_restore (M := prog) (self' := r1 b)
    (next := r2 b) (t := .X) (a := .F) (dt := Sym.bit?) (et := Sym.bit) (ga := Sym.bit)
    (da := Sym.bit?) (h1 b) (by decide) (fun _ => rfl) bit_inv u cp (u.map Sym.bit) A [] v₁ S₁
    (isBitBlock_map u) hcu (by simp [h1X, hx]) (by simp [h1F]) rfl
  obtain ⟨v₃, S₃, r₃, h3Y, h3V, h3k⟩ := moveB_restore (M := prog) (self' := r2 b)
    (next := nx b) (t := .Y) (a := .V) (dt := Sym.bit?) (et := Sym.bit) (ga := Sym.bit)
    (da := Sym.bit?) (h2 b) (by decide) (fun _ => rfl) bit_inv w cp (w.map Sym.bit) B [] v₂ S₂
    (isBitBlock_map w) hcw (by simp [h2k, h1Y]) (by simp [h2k, h1V]) rfl
  have hS : S₃ = s.stk := by
    funext k; cases k <;> simp [h3Y, h3V, h3k, h2X, h2F, h2k, h1k, hf, hv, hx]
  rw [hS] at r₃
  refine ⟨v₃, ((r₁.trans r₂).trans r₃).le ?_⟩
  have := hcw.length_le
  omega

/-! ### Phase A: tokens to `F`, clause counts, distinct variables -/

/-- **Name of a variable in the HAMPATH emitter.** The name of a variable $x \in \mathbb{N}$ is the
list of name-bit symbols $\mathrm{bit}(b_0), \dots, \mathrm{bit}(b_{k-1})$, where
$b_0 \cdots b_{k-1}$ is the binary encoding of $x$, least significant bit first (the empty list
for $x = 0$). -/
abbrev name (x : ℕ) : List Sym := (encodeNat x).map Sym.bit

/-- **Variable stack of the HAMPATH emitter.** For a list $x_1, \dots, x_k$ of variables (natural
numbers), the variable stack is the list of symbols obtained by concatenating, for
$i = 1, \dots, k$ in order, the name bits of $x_i$ followed by the separator symbol
$\mathrm{cl}$. With the head of the list on top, $x_1$ is the top entry and each name sits above
its separator. -/
def vstk (vs : List ℕ) : List Sym := vs.flatMap fun x => name x ++ [Sym.cl]

/-- **Variable-stack symbols of the HAMPATH emitter.** A token symbol is a variable-stack symbol
when it is a name bit $\mathrm{bit}(b)$ for some bit $b$ or the separator $\mathrm{cl}$; the
polarity markers, the value markers and the dead marker are not. -/
def isVS : Sym → Bool
  | .bit _ | .cl => true
  | _ => false

theorem isVS_vstk (vs : List ℕ) : ∀ x ∈ vstk vs, isVS x = true := by
  intro x hx
  simp only [vstk, List.mem_flatMap, List.mem_append, List.mem_map, List.mem_singleton] at hx
  obtain ⟨_, -, ⟨b, -, rfl⟩ | rfl⟩ := hx <;> rfl

section PhaseA

variable (s : MS) (v : Bool)

theorem a0_nil (h : s.t = []) : Run prog 1 ⟨some .a0, v, s.stk⟩ ⟨some .b0, true, s.stk⟩ :=
  Run.single (by simp [prog, TM2.stepAux, h])

theorem a0_cl (R : List Sym) (h : s.t = .cl :: R) : Run prog 1 ⟨some .a0, v, s.stk⟩
    ⟨some .a0, true, {s with t := R, f := .cl :: s.f, c := s.c + 1, mm := s.mm + 3}.stk⟩ :=
  Run.single (by
    simp only [prog, TM2.stepAux, stk_T, h, List.head?_cons, Option.isNone_some, id_eq, BEq.rfl,
      List.tail_cons, upd_T, ne_eq, reduceCtorEq, not_false_eq_true, update_of_ne, stk_F, upd_F,
      stk_C, stepAux_pushList, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append, stk_M, Option.some_beq_some, sym_beq, decide_false, cond_eq_ite,
      ↓reduceIte, Bool.false_eq_true, TM2.Cfg.mk.injEq, true_and]
    funext k; cases k <;> simp [List.replicate_succ])

theorem a0_lit (p : Bool) (R : List Sym) (h : s.t = .lit p :: R) :
    Run prog 1 ⟨some .a0, v, s.stk⟩ ⟨some .anm, p, {s with t := R, f := .lit p :: s.f}.stk⟩ :=
  Run.single (by cases p <;> simp [prog, TM2.stepAux, h])

theorem aw_nil (f : Bool) (h : s.v = []) :
    Run prog 1 ⟨some (.aw f), v, s.stk⟩ ⟨some (.ab f), true, s.stk⟩ :=
  Run.single (by simp [prog, TM2.stepAux, h])

theorem aw_cons (f : Bool) (x : Sym) (R : List Sym) (h : s.v = x :: R) :
    Run prog 1 ⟨some (.aw f), v, s.stk⟩ ⟨some (.ac f), false, s.stk⟩ :=
  Run.single (by simp [prog, TM2.stepAux, h])

theorem asep_step (f : Bool) (R : List Sym) (h : s.v = .cl :: R) :
    Run prog 1 ⟨some (.asep f), v, s.stk⟩ ⟨some (.aw f), v, {s with v := R, w := .cl :: s.w}.stk⟩ :=
  Run.single (by simp [prog, TM2.stepAux, h])

theorem ab_nil_true (h : s.w = []) :
    Run prog 1 ⟨some (.ab true), v, s.stk⟩ ⟨some .a0, true, s.stk⟩ :=
  Run.single (by simp [prog, TM2.stepAux, h])

theorem ab_nil_false (h : s.w = []) :
    Run prog 1 ⟨some (.ab false), v, s.stk⟩ ⟨some .ad2, true, {s with v := .cl :: s.v}.stk⟩ :=
  Run.single (by simp [prog, TM2.stepAux, h])

theorem ab_step (f : Bool) (x : Sym) (hx : isVS x = true) (R : List Sym) (h : s.w = x :: R) :
    ∃ v', Run prog 1 ⟨some (.ab f), v, s.stk⟩
      ⟨some (.ab f), v', {s with w := R, v := x :: s.v}.stk⟩ := by
  cases x with
  | bit b => exact ⟨b, Run.single (by cases b <;> simp [prog, TM2.stepAux, h])⟩
  | cl => exact ⟨true, Run.single (by simp [prog, TM2.stepAux, h])⟩
  | _ => simp [isVS] at hx

end PhaseA

/-- **HAMPATH emitter, phase A: moving the walk stack back onto the variable stack.** Let $f$ be
a Boolean, let $L$ be a list of symbols each of which is a name bit or the separator
$\mathrm{cl}$, and let $s$ be a quiescent state of the HAMPATH emitter whose stack $W$ is $L$.
Then for every value $v$ of the machine's Boolean variable there is a value $v'$ such that the
emitter goes in exactly $|L|$ steps from label $\mathrm{ab}(f)$, variable $v$ and the stacks of
$s$ to label $\mathrm{ab}(f)$, variable $v'$ and the stacks of the state obtained from $s$ by
emptying $W$ and replacing $V$ by the reverse of $L$ followed by the old contents of $V$. -/
theorem ab_run (f : Bool) : ∀ (L : List Sym), (∀ x ∈ L, isVS x = true) → ∀ (s : MS) (v : Bool),
    s.w = L → ∃ v', Run prog L.length ⟨some (.ab f), v, s.stk⟩
      ⟨some (.ab f), v', {s with w := [], v := L.reverse ++ s.v}.stk⟩ := by
  intro L
  induction L with
  | nil =>
      intro _ s v h
      have e : ({s with w := [], v := ([] : List Sym).reverse ++ s.v} : MS) = s := by
        cases s; simp_all
      exact ⟨v, by rw [e]; exact Run.zero _⟩
  | cons x L ih =>
      intro hL s v h
      obtain ⟨v₁, r₁⟩ := ab_step s v f x (hL x (by simp)) L h
      obtain ⟨v₂, r₂⟩ := ih (fun y hy => hL y (by simp [hy])) {s with w := L, v := x :: s.v} v₁
        rfl
      exact ⟨v₂, by simpa [Nat.add_comm] using r₁.trans r₂⟩

/-- **HAMPATH emitter, phase A: searching the variable stack for a name.** For $y \in \mathbb{N}$
write $\mathrm{name}(y)$ for the canonical binary encoding of $y$ as name-bit symbols, and for a
list $\mathit{vs}$ of naturals write $\mathrm{vstk}(\mathit{vs})$ for the variable stack: the
names of the entries of $\mathit{vs}$, each followed by the separator $\mathrm{cl}$. Let
$x \in \mathbb{N}$ and let $A$ be a list of symbols that is empty or does not start with a name
bit. Then for every list $\mathit{vs}$ of naturals, every Boolean $f$, every quiescent state $s$
of the HAMPATH emitter whose stack $F$ is $\mathrm{name}(x)$ followed by $A$, whose stack $V$ is
$\mathrm{vstk}(\mathit{vs})$ and whose stack $X$ is empty, and every value $v$ of the machine's
Boolean variable, writing $g$ for the Boolean that is true exactly when $f$ is true or $x$
occurs in $\mathit{vs}$, there is a value $v'$ such that the emitter goes in at most
$6|\mathrm{vstk}(\mathit{vs})| + 1$ steps from label $\mathrm{aw}(f)$, variable $v$ and the
stacks of $s$ to label $\mathrm{ab}(g)$, variable $v'$ and the stacks of the state obtained
from $s$ by emptying $V$ and replacing $W$ by the reverse of $\mathrm{vstk}(\mathit{vs})$
followed by the old contents of $W$. -/
theorem aw_run (x : ℕ) (A : List Sym) (hA : A.head?.bind Sym.bit? = none) :
    ∀ (vs : List ℕ) (f : Bool) (s : MS) (v : Bool), s.f = name x ++ A → s.v = vstk vs →
      s.x = [] →
      ∃ v', RunLe prog (6 * (vstk vs).length + 1) ⟨some (.aw f), v, s.stk⟩
        ⟨some (.ab (f || decide (x ∈ vs))), v',
          {s with v := [], w := (vstk vs).reverse ++ s.w}.stk⟩ := by
  intro vs
  induction vs with
  | nil =>
      intro f s v _ hv _
      have e : ({s with v := [], w := (vstk []).reverse ++ s.w} : MS) = s := by
        cases s; simp_all [vstk]
      exact ⟨true, runLe_cast ((aw_nil s v f hv).le le_rfl) (by simp) (by simp [e])⟩
  | cons y vs ih =>
      intro f s v hf hv hx
      have hv' : s.v = name y ++ Sym.cl :: vstk vs := by simp [hv, vstk]
      obtain ⟨x0, R0, hx0⟩ : ∃ x0 R0, s.v = x0 :: R0 := by
        rw [hv']
        cases h : encodeNat y with
        | nil => exact ⟨Sym.cl, vstk vs, by simp [name, h]⟩
        | cons b t => exact ⟨Sym.bit b, t.map Sym.bit ++ Sym.cl :: vstk vs, by simp [name, h]⟩
      have r₁ := aw_cons s v f x0 R0 hx0
      obtain ⟨v₂, r₂⟩ := cmpR_run (lc := .ac f) (r1 := .ar1) (r2 := .ar2) (nx := .amv)
        (bT := true) (bF := f) rfl (fun _ => rfl) (fun _ => rfl) s false (encodeNat x)
        (encodeNat y) A (Sym.cl :: vstk vs) hA rfl hf hv' hx
      set f' := if encodeNat x = encodeNat y then true else f with hf'
      obtain ⟨v₃, S₃, r₃, h3V, h3W, h3k⟩ := moveB_run (M := prog) (self := .amv f')
        (next := .asep f') (a := .V) (b := .W) (d := Sym.bit?) (g := Sym.bit) rfl (by decide)
        (encodeNat y) (name y) (Sym.cl :: vstk vs) v₂ s.stk (by simp [hv'])
        (isBitBlock_map _) rfl
      have hS₃ : S₃ = {s with v := Sym.cl :: vstk vs, w := (name y).reverse ++ s.w}.stk := by
        funext k; cases k <;> simp [h3V, h3W, h3k]
      rw [hS₃] at r₃
      have r₄ := asep_step {s with v := Sym.cl :: vstk vs, w := (name y).reverse ++ s.w} v₃ f'
        (vstk vs) rfl
      obtain ⟨v₅, r₅⟩ := ih f' {s with v := vstk vs, w := Sym.cl :: ((name y).reverse ++ s.w)}
        v₃ hf rfl hx
      have hff : (f' || decide (x ∈ vs)) = (f || decide (x ∈ y :: vs)) := by
        rw [hf']
        by_cases hxy : x = y
        · subst hxy; simp
        · have : encodeNat x ≠ encodeNat y := fun h => hxy (encodeNat_inj.1 h)
          simp [this, hxy]
      rw [hff] at r₅
      refine ⟨v₅, runLe_cast ((r₁.le le_rfl).trans (r₂.trans (((r₃.trans r₄).le le_rfl).trans
        r₅))) ?_ ?_⟩
      · simp [vstk]; omega
      · simp [vstk, List.reverse_append]

/-- **HAMPATH emitter, phase A: copying a reversed name onto two stacks.** Let $u$ be a list of
bits and let $s$ be a quiescent state of the HAMPATH emitter whose stack $X$ holds $u$ as
name-bit symbols. Then for every value $v$ of the machine's Boolean variable there is a value
$v'$ such that the emitter goes in exactly $|u| + 1$ steps from label $\mathrm{ad3}$, variable
$v$ and the stacks of $s$ to label $\mathrm{a0}$, variable $v'$ and the stacks of the state
obtained from $s$ by emptying $X$ and replacing each of $F$ and $V$ by the reverse of $u$ (as
name-bit symbols) followed by its old contents. -/
theorem ad3_run : ∀ (u : List Bool) (s : MS) (v : Bool), s.x = u.map Sym.bit →
    ∃ v', Run prog (u.length + 1) ⟨some .ad3, v, s.stk⟩ ⟨some .a0, v',
      { s with
        x := [], f := (u.map Sym.bit).reverse ++ s.f, v := (u.map Sym.bit).reverse ++ s.v }.stk⟩ :=
    by
  intro u
  induction u with
  | nil =>
      intro s v h
      have e : ({ s with
          x := [], f := (([] : List Bool).map Sym.bit).reverse ++ s.f,
          v := (([] : List Bool).map Sym.bit).reverse ++ s.v } : MS) = s := by
        cases s; simp_all
      exact ⟨false, by rw [e]; exact Run.single (by simp [prog, TM2.stepAux, h, isBit])⟩
  | cons b u ih =>
      intro s v h
      have r₁ : Run prog 1 ⟨some .ad3, v, s.stk⟩ ⟨some .ad3, b,
          { s with x := u.map Sym.bit, f := Sym.bit b :: s.f, v := Sym.bit b :: s.v }.stk⟩ :=
        Run.single (by cases b <;> simp [prog, TM2.stepAux, h, isBit, bitOf, Sym.bit?])
      obtain ⟨v₂, r₂⟩ := ih { s with
        x := u.map Sym.bit, f := Sym.bit b :: s.f, v := Sym.bit b :: s.v } b rfl
      have e : ({ ({ s with x := u.map Sym.bit, f := Sym.bit b :: s.f, v := Sym.bit b :: s.v } : MS)
          with
          x := [], f := (u.map Sym.bit).reverse ++ (Sym.bit b :: s.f),
          v := (u.map Sym.bit).reverse ++ (Sym.bit b :: s.v) } : MS) =
          { s with
            x := [], f := ((b :: u).map Sym.bit).reverse ++ s.f,
            v := ((b :: u).map Sym.bit).reverse ++ s.v } := by simp
      rw [e] at r₂
      exact ⟨v₂, (r₁.trans r₂).of_eq (by simp; omega)⟩

theorem vstk_insV_le (x : ℕ) (vs : List ℕ) :
    (vstk (insV x vs)).length ≤ (vstk vs).length + (encodeNat x).length + 1 := by
  unfold insV; split <;> simp [vstk] <;> omega

theorem vstk_lits_le (Ls : List (ℕ × Bool)) (vs : List ℕ) :
    (vstk (Ls.foldr (fun (l : ℕ × Bool) vs => insV l.1 vs) vs)).length ≤
      (vstk vs).length + (Ls.flatMap Check.litRev).length := by
  induction Ls with
  | nil => simp
  | cons l' Ls ih' =>
      have := vstk_insV_le l'.1 (Ls.foldr (fun (l : ℕ × Bool) vs => insV l.1 vs) vs)
      have := Check.litRev_length l'
      simp only [List.foldr_cons, List.flatMap_cons, List.length_append] at this ih' ⊢
      omega

/-- **HAMPATH emitter, phase A: one literal.** For $x \in \mathbb{N}$ write $\mathrm{name}(x)$
for the canonical binary encoding of $x$ as name-bit symbols. Let $\ell = (x, p)$ be a literal
with variable $x$ and polarity $p$: its tokens are $\mathrm{name}(x)$ followed by the polarity
marker $\mathrm{lit}(p)$, and its reversed tokens $r_\ell$ are $\mathrm{lit}(p)$ followed by the
reverse of $\mathrm{name}(x)$. For a list $\mathit{vs}$ of naturals write
$\mathrm{vstk}(\mathit{vs})$ for the names of the entries of $\mathit{vs}$, each followed by the
separator $\mathrm{cl}$, and $\mathrm{ins}(x, \mathit{vs})$ for $\mathit{vs}$ if $x$ occurs in
$\mathit{vs}$ and for $\mathit{vs}$ with $x$ added at the front otherwise. Let $R$ be a list of
symbols that is empty or does not start with a name bit, let $\mathit{vs}$ be a list of
naturals, and let $s$ be a quiescent state of the HAMPATH emitter whose stack $T$ is $r_\ell$
followed by $R$, whose stack $V$ is $\mathrm{vstk}(\mathit{vs})$ and whose stacks $W$ and $X$
are empty. Then for every value $v$ of the machine's Boolean variable there is a value $v'$ such
that the emitter goes in at most $8|\mathrm{vstk}(\mathit{vs})| + 4|r_\ell| + 8$ steps from
label $\mathrm{a0}$, variable $v$ and the stacks of $s$ to label $\mathrm{a0}$, variable $v'$
and the stacks of the state obtained from $s$ by setting $T$ to $R$, $F$ to the tokens of $\ell$
followed by the old contents of $F$, and $V$ to $\mathrm{vstk}(\mathrm{ins}(x, \mathit{vs}))$. -/
theorem alit_run (l : ℕ × Bool) (R : List Sym) (hR : R.head?.bind Sym.bit? = none)
    (vs : List ℕ) (s : MS) (v : Bool) (ht : s.t = Check.litRev l ++ R) (hv : s.v = vstk vs)
    (hw : s.w = []) (hx : s.x = []) :
    ∃ v', RunLe prog (8 * (vstk vs).length + 4 * (Check.litRev l).length + 8)
      ⟨some .a0, v, s.stk⟩
      ⟨some .a0, v', {s with t := R, f := litToks l ++ s.f, v := vstk (insV l.1 vs)}.stk⟩ := by
  obtain ⟨x, p⟩ := l
  have hlen : (Check.litRev (x, p)).length = (encodeNat x).length + 1 := Check.litRev_length _
  have r₁ := a0_lit s v p ((name x).reverse ++ R) (by simp [ht, Check.litRev])
  set s₁ := {s with t := (name x).reverse ++ R, f := Sym.lit p :: s.f}
  obtain ⟨v₂, S₂, r₂, h2T, h2F, h2k⟩ := moveB_run (M := prog) (self := .anm)
    (next := .aw false) (a := .T) (b := .F) (d := Sym.bit?) (g := Sym.bit) rfl (by decide)
    (encodeNat x).reverse (name x).reverse R p s₁.stk rfl (isBitBlock_rev _) hR
  have hS₂ : S₂ = {s₁ with t := R, f := name x ++ Sym.lit p :: s.f}.stk := by
    funext k; cases k <;> simp [h2T, h2F, h2k, s₁, List.map_reverse]
  rw [hS₂] at r₂
  set s₂ := {s₁ with t := R, f := name x ++ Sym.lit p :: s.f}
  obtain ⟨v₃, r₃⟩ := aw_run x (Sym.lit p :: s.f) rfl vs false s₂ v₂ rfl (by simp [s₂, s₁, hv])
    (by simp [s₂, s₁, hx])
  obtain ⟨v₄, r₄⟩ := ab_run (false || decide (x ∈ vs)) ((vstk vs).reverse ++ s₂.w)
    (fun y hy => by
      simp only [s₂, s₁, hw, List.append_nil, List.mem_reverse] at hy
      exact isVS_vstk vs y hy)
    {s₂ with v := [], w := (vstk vs).reverse ++ s₂.w} v₃ rfl
  set s₄ : MS := {s₂ with w := [], v := ((vstk vs).reverse ++ s₂.w).reverse ++ []} with hs₄
  have hs₄v : s₄.v = vstk vs := by simp [s₄, s₂, s₁, hw]
  have hlt : litToks (x, p) = name x ++ [Sym.lit p] := rfl
  by_cases hm : x ∈ vs
  · have r₅ := ab_nil_true s₄ v₄ rfl
    simp only [hm, decide_true, Bool.false_or] at r₃ r₄
    refine ⟨true, runLe_cast ((r₁.trans r₂).le le_rfl |>.trans
      (r₃.trans ((r₄.trans r₅).le le_rfl))) ?_ ?_⟩
    · simp [s₂, s₁, hw]; omega
    · congr 2
      simp [s₄, s₂, s₁, hlt, insV, hm, hw, hx]
  · have r₅ := ab_nil_false s₄ v₄ rfl
    simp only [hm, decide_false, Bool.false_or] at r₃ r₄
    set s₅ := {s₄ with v := Sym.cl :: s₄.v}
    obtain ⟨v₆, S₆, r₆, h6F, h6X, h6k⟩ := moveB_run (M := prog) (self := .ad2)
      (next := .ad3) (a := .F) (b := .X) (d := Sym.bit?) (g := Sym.bit) rfl (by decide)
      (encodeNat x) (name x) (Sym.lit p :: s.f) true s₅.stk (by simp [s₅, s₄, s₂])
      (isBitBlock_map _) rfl
    have hS₆ : S₆ = {s₅ with f := Sym.lit p :: s.f, x := (name x).reverse}.stk := by
      funext k; cases k <;> simp [h6F, h6X, h6k, s₅, s₄, s₂, s₁, hx]
    rw [hS₆] at r₆
    obtain ⟨v₇, r₇⟩ := ad3_run (encodeNat x).reverse
      {s₅ with f := Sym.lit p :: s.f, x := (name x).reverse} v₆ (by simp [List.map_reverse])
    refine ⟨v₇, runLe_cast ((r₁.trans r₂).le le_rfl |>.trans
      (r₃.trans ((((r₄.trans r₅).trans r₆).trans r₇).le le_rfl))) ?_ ?_⟩
    · simp [s₂, s₁, hw]; omega
    · congr 2
      simp [s₅, s₄, s₂, s₁, hlt, insV, hm, hw, hx, vstk, List.map_reverse]

/-- **HAMPATH emitter, phase A: the literals of a clause.** Notation: $\mathrm{name}(x)$ is the
canonical binary encoding of $x \in \mathbb{N}$ as name-bit symbols; a literal $\ell = (x, p)$
has tokens $\mathrm{name}(x)$ followed by the polarity marker $\mathrm{lit}(p)$ and reversed
tokens $r_\ell$, namely $\mathrm{lit}(p)$ followed by the reverse of $\mathrm{name}(x)$;
$\mathrm{vstk}(\mathit{vs})$ is the list of the names of the entries of a list $\mathit{vs}$ of
naturals, each followed by the separator $\mathrm{cl}$; and $\mathrm{ins}(x, \mathit{vs})$ is
$\mathit{vs}$ if $x$ occurs in $\mathit{vs}$ and $\mathit{vs}$ with $x$ added at the front
otherwise. Let $L_b \in \mathbb{N}$, let $\ell_1, \dots, \ell_k$ be literals with variables
$x_1, \dots, x_k$, let $n = |r_{\ell_1}| + \dots + |r_{\ell_k}|$, and let $R$ be a list of
symbols that is empty or does not start with a name bit. Then for every list $\mathit{vs}$ of
naturals with $|\mathrm{vstk}(\mathit{vs})| + n \le L_b$, every quiescent state $s$ of the
HAMPATH emitter whose stack $T$ is the concatenation of $r_{\ell_k}, \dots, r_{\ell_1}$ followed
by $R$, whose stack $V$ is $\mathrm{vstk}(\mathit{vs})$ and whose stacks $W$ and $X$ are empty,
and every value $v$ of the machine's Boolean variable, there is a value $v'$ such that the
emitter goes in at most $n(8L_b + 12)$ steps from label $\mathrm{a0}$, variable $v$ and the
stacks of $s$ to label $\mathrm{a0}$, variable $v'$ and the stacks of the state obtained from
$s$ by setting $T$ to $R$, $F$ to the concatenated tokens of $\ell_1, \dots, \ell_k$ followed by
the old contents of $F$, and $V$ to
$\mathrm{vstk}(\mathrm{ins}(x_1, \dots \mathrm{ins}(x_k, \mathit{vs}) \dots))$. -/
theorem alits_run (Lb : ℕ) : ∀ (Ls : List (ℕ × Bool)) (R : List Sym),
    R.head?.bind Sym.bit? = none → ∀ (vs : List ℕ) (s : MS) (v : Bool),
    s.t = Ls.reverse.flatMap Check.litRev ++ R → s.v = vstk vs → s.w = [] → s.x = [] →
    (vstk vs).length + (Ls.flatMap Check.litRev).length ≤ Lb →
    ∃ v', RunLe prog ((Ls.flatMap Check.litRev).length * (8 * Lb + 12)) ⟨some .a0, v, s.stk⟩
      ⟨some .a0, v', { s with
        t := R, f := Ls.flatMap litToks ++ s.f,
        v := vstk (Ls.foldr (fun (l : ℕ × Bool) vs => insV l.1 vs) vs) }.stk⟩ := by
  intro Ls
  induction Ls with
  | nil =>
      intro R _ vs s v ht hv _ _ _
      have e : ({ s with
          t := R, f := ([] : List (ℕ × Bool)).flatMap litToks ++ s.f,
          v := vstk (([] : List (ℕ × Bool)).foldr (fun (l : ℕ × Bool) vs => insV l.1 vs) vs) } :
          MS) = s := by
        cases s; simp_all
      exact ⟨v, runLe_cast (RunLe.refl 0 _) (Nat.zero_le _) (by rw [e])⟩
  | cons l Ls ih =>
      intro R hR vs s v ht hv hw hx hb
      have hl : (Check.litRev l).length = (encodeNat l.1).length + 1 := Check.litRev_length l
      simp only [List.flatMap_cons, List.length_append] at hb
      obtain ⟨v₁, r₁⟩ := ih (Check.litRev l ++ R) (by simp [Check.litRev, Sym.bit?]) vs s v
        (by simp [ht]) hv hw hx (by omega)
      set vs' := Ls.foldr (fun (l : ℕ × Bool) vs => insV l.1 vs) vs
      have hvs' := vstk_lits_le Ls vs
      obtain ⟨v₂, r₂⟩ := alit_run l R hR vs' { s with
        t := Check.litRev l ++ R, f := Ls.flatMap litToks ++ s.f, v := vstk vs' } v₁ rfl rfl hw hx
      refine ⟨v₂, runLe_cast (r₁.trans r₂) ?_ ?_⟩
      · simp only [List.flatMap_cons, List.length_append]
        nlinarith
      · simp [vs', List.append_assoc]

theorem clRev_len (C : CNFClause) :
    (Check.clRev C).length = (C.flatMap Check.litRev).length + 1 := by
  simp [Check.clRev, List.length_flatMap, List.map_reverse, List.sum_reverse]

/-- **HAMPATH emitter, phase A: one clause.** Notation: $\mathrm{name}(x)$ is the canonical
binary encoding of $x \in \mathbb{N}$ as name-bit symbols; a literal $\ell = (x, p)$ has tokens
$\mathrm{name}(x)$ followed by the polarity marker $\mathrm{lit}(p)$ and reversed tokens
$r_\ell$, namely $\mathrm{lit}(p)$ followed by the reverse of $\mathrm{name}(x)$;
$\mathrm{vstk}(\mathit{vs})$ is the list of the names of the entries of a list $\mathit{vs}$ of
naturals, each followed by the separator $\mathrm{cl}$; and $\mathrm{ins}(x, \mathit{vs})$ is
$\mathit{vs}$ if $x$ occurs in $\mathit{vs}$ and $\mathit{vs}$ with $x$ added at the front
otherwise. Let $L_b \in \mathbb{N}$ and let $C$ be a clause with literals $\ell_1, \dots, \ell_k$
and variables $x_1, \dots, x_k$. The tokens of $C$ are the concatenated tokens of
$\ell_1, \dots, \ell_k$ followed by $\mathrm{cl}$, and its reversed tokens $r_C$ are
$\mathrm{cl}$ followed by the concatenation of $r_{\ell_k}, \dots, r_{\ell_1}$. Let $R$ be a list
of symbols that is empty or starts with $\mathrm{cl}$, let $\mathit{vs}$ be a list of naturals
with $|\mathrm{vstk}(\mathit{vs})| + |r_C| \le L_b$, and let $s$ be a quiescent state of the
HAMPATH emitter whose stack $T$ is $r_C$ followed by $R$, whose stack $V$ is
$\mathrm{vstk}(\mathit{vs})$ and whose stacks $W$ and $X$ are empty. Then for every value $v$ of
the machine's Boolean variable there is a value $v'$ such that the emitter goes in at most
$|r_C|(8L_b + 12)$ steps from label $\mathrm{a0}$, variable $v$ and the stacks of $s$ to label
$\mathrm{a0}$, variable $v'$ and the stacks of the state obtained from $s$ by setting $T$ to
$R$, $F$ to the tokens of $C$ followed by the old contents of $F$, and $V$ to
$\mathrm{vstk}(\mathrm{ins}(x_1, \dots \mathrm{ins}(x_k, \mathit{vs}) \dots))$, and by
increasing the clause count by $1$ and the triple clause count by $3$. -/
theorem aclause_run (Lb : ℕ) (C : CNFClause) (R : List Sym) (hR : R = [] ∨ R.head? = some .cl)
    (vs : List ℕ) (s : MS) (v : Bool) (ht : s.t = Check.clRev C ++ R) (hv : s.v = vstk vs)
    (hw : s.w = []) (hx : s.x = []) (hb : (vstk vs).length + (Check.clRev C).length ≤ Lb) :
    ∃ v', RunLe prog ((Check.clRev C).length * (8 * Lb + 12)) ⟨some .a0, v, s.stk⟩
      ⟨some .a0, v', { s with
        t := R, f := clauseToks C ++ s.f, v := vstk ((C.map Prod.fst).foldr insV vs),
        c := s.c + 1, mm := s.mm + 3 }.stk⟩ := by
  have hRb : R.head?.bind Sym.bit? = none := by rcases hR with rfl | h <;> simp [Sym.bit?, *]
  have r₁ := a0_cl s v (C.reverse.flatMap Check.litRev ++ R) (by simp [ht, Check.clRev])
  rw [clRev_len] at hb ⊢
  obtain ⟨v₂, r₂⟩ := alits_run Lb C R hRb vs { s with
    t := C.reverse.flatMap Check.litRev ++ R, f := Sym.cl :: s.f, c := s.c + 1,
    mm := s.mm + 3 } true rfl hv hw hx (by omega)
  refine ⟨v₂, runLe_cast ((r₁.le le_rfl).trans r₂) (by nlinarith) ?_⟩
  simp [clauseToks, foldr_lits]

theorem vstk_varsOf_le (φ : CNF) (vs : List ℕ) :
    (vstk ((varsOf φ).foldr insV vs)).length ≤
      (vstk vs).length + (φ.reverse.flatMap Check.clRev).length := by
  induction φ with
  | nil => simp [varsOf]
  | cons C φ ih =>
      have h := vstk_lits_le C ((varsOf φ).foldr insV vs)
      rw [foldr_lits] at h
      have := clRev_len C
      simp only [varsOf_cons, List.foldr_append, List.reverse_cons, List.flatMap_append,
        List.length_append, List.flatMap_cons, List.flatMap_nil, List.append_nil] at h ih ⊢
      omega

/-- **HAMPATH emitter, phase A: the clauses of a formula.** Notation: $\mathrm{name}(x)$ is the
canonical binary encoding of $x \in \mathbb{N}$ as name-bit symbols; a literal $\ell = (x, p)$
has tokens $\mathrm{name}(x)$ followed by the polarity marker $\mathrm{lit}(p)$; a clause $C$
with literals $\ell_1, \dots, \ell_k$ has tokens the concatenated tokens of
$\ell_1, \dots, \ell_k$ followed by the separator $\mathrm{cl}$, and reversed tokens $r_C$,
namely $\mathrm{cl}$ followed by, for $\ell = \ell_k, \dots, \ell_1$ in turn,
$\mathrm{lit}(p)$ and the reverse of $\mathrm{name}(x)$; $\mathrm{vstk}(\mathit{vs})$ is the
list of the names of the entries of a list $\mathit{vs}$ of naturals, each followed by
$\mathrm{cl}$; and $\mathrm{ins}(x, \mathit{vs})$ is $\mathit{vs}$ if $x$ occurs in
$\mathit{vs}$ and $\mathit{vs}$ with $x$ added at the front otherwise. Let $L_b \in \mathbb{N}$,
let $\varphi$ be a CNF formula with clauses $C_1, \dots, C_m$, whose tokens are the
concatenated tokens of $C_1, \dots, C_m$, let $y_1, \dots, y_n$ be the variables of the literals
of $\varphi$ in order of occurrence (with repetitions), let
$N = |r_{C_1}| + \dots + |r_{C_m}|$, and let $R$ be a list of symbols that is empty or starts
with $\mathrm{cl}$. Then for every list $\mathit{vs}$ of naturals with
$|\mathrm{vstk}(\mathit{vs})| + N \le L_b$, every quiescent state $s$ of the HAMPATH emitter
whose stack $T$ is the concatenation of $r_{C_m}, \dots, r_{C_1}$ followed by $R$, whose stack
$V$ is $\mathrm{vstk}(\mathit{vs})$ and whose stacks $W$ and $X$ are empty, and every value $v$
of the machine's Boolean variable, there is a value $v'$ such that the emitter goes in at most
$N(8L_b + 12)$ steps from label $\mathrm{a0}$, variable $v$ and the stacks of $s$ to label
$\mathrm{a0}$, variable $v'$ and the stacks of the state obtained from $s$ by setting $T$ to
$R$, $F$ to the tokens of $\varphi$ followed by the old contents of $F$, and $V$ to
$\mathrm{vstk}(\mathrm{ins}(y_1, \dots \mathrm{ins}(y_n, \mathit{vs}) \dots))$, and by
increasing the clause count by $m$ and the triple clause count by $3m$. -/
theorem aformula_run (Lb : ℕ) : ∀ (φ : CNF) (R : List Sym), (R = [] ∨ R.head? = some .cl) →
    ∀ (vs : List ℕ) (s : MS) (v : Bool), s.t = φ.reverse.flatMap Check.clRev ++ R →
    s.v = vstk vs → s.w = [] → s.x = [] →
    (vstk vs).length + (φ.reverse.flatMap Check.clRev).length ≤ Lb →
    ∃ v', RunLe prog ((φ.reverse.flatMap Check.clRev).length * (8 * Lb + 12))
      ⟨some .a0, v, s.stk⟩
      ⟨some .a0, v', { s with
        t := R, f := toks φ ++ s.f, v := vstk ((varsOf φ).foldr insV vs),
        c := s.c + φ.length, mm := s.mm + 3 * φ.length }.stk⟩ := by
  intro φ
  induction φ with
  | nil =>
      intro R _ vs s v ht hv _ _ _
      have e : ({ s with
          t := R, f := toks [] ++ s.f, v := vstk ((varsOf []).foldr insV vs),
          c := s.c + List.length ([] : CNF), mm := s.mm + 3 * List.length ([] : CNF) } : MS) =
          s := by
        cases s; simp_all [toks, varsOf]
      exact ⟨v, runLe_cast (RunLe.refl 0 _) (Nat.zero_le _) (by rw [e])⟩
  | cons C φ ih =>
      intro R hR vs s v ht hv hw hx hb
      have hl : ((C :: φ).reverse.flatMap Check.clRev).length =
          (φ.reverse.flatMap Check.clRev).length + (Check.clRev C).length := by simp
      obtain ⟨v₁, r₁⟩ := ih (Check.clRev C ++ R) (Or.inr rfl) vs s v (by simp [ht]) hv hw hx
        (by omega)
      have hvs := vstk_varsOf_le φ vs
      obtain ⟨v₂, r₂⟩ := aclause_run Lb C R hR ((varsOf φ).foldr insV vs) { s with
        t := Check.clRev C ++ R, f := toks φ ++ s.f, v := vstk ((varsOf φ).foldr insV vs),
        c := s.c + φ.length, mm := s.mm + 3 * φ.length } v₁ rfl rfl hw hx (by omega)
      refine ⟨v₂, runLe_cast (r₁.trans r₂) (by rw [hl]; nlinarith) ?_⟩
      simp [toks, varsOf_cons, List.foldr_append, List.append_assoc]
      congr 2

/-- **Initial state of the HAMPATH emitter.** For a CNF formula $\varphi$ and an output list $o$,
the initial state is the quiescent state whose token stack holds the tokens of $\varphi$ in
reverse reading order, whose output stack is $o$, and all of whose other stacks are empty and
counters zero. -/
def initMS (φ : CNF) (o : List Bool) : MS :=
  ⟨(toks φ).reverse, o, [], [], [], [], [], [], 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- **The emitter state before the diamonds.** For a CNF formula $\varphi$ with $m$ clauses and an
output list $o$, this is the quiescent state whose output stack is $o$, whose stack $F$ holds the
tokens of $\varphi$ in reading order, whose stack $V$ is the variable stack of the distinct
variables of $\varphi$ (each kept at its last occurrence), whose clause count and diamond top are
both $m$, whose count of three times the clauses is $3m$, and all of whose other stacks are empty
and other counters zero.

It is the state that phase A, followed by setting the diamond top, reaches from the initial
state. -/
def diaMS (φ : CNF) (o : List Bool) : MS :=
  ⟨[], o, toks φ, vstk (hamVars φ), [], [], [], [], φ.length, 3 * φ.length, φ.length, 0, 0, 0,
    0, 0⟩

/-- **Phase A of the HAMPATH emitter.** Let $\varphi$ be a CNF formula with $m$ clauses whose token
list has length $L$, let $o$ be a list of bits and let $v$ be a bit. Started at label
$\mathrm{a0}$ with internal state $v$ and the stacks of the initial emitter state of $\varphi$ and
$o$ (the token stack holding the tokens of $\varphi$ reversed, the output stack holding $o$, and
everything else empty), the emitter reaches, within at most $L(8L + 12) + 2m + 3$ steps, label
$\mathrm{h0}$ with some internal state and the stacks of the emitter state of $\varphi$ and $o$
after phase A (the tokens of $\varphi$ on $F$, the variable stack of the distinct variables of
$\varphi$ on $V$, $m$ on the counters $C$ and $P$, $3m$ on $M$, $o$ on the output stack, and
everything else empty). -/
theorem phaseA_run (φ : CNF) (o : List Bool) (v : Bool) :
    ∃ v', RunLe prog ((toks φ).length * (8 * (toks φ).length + 12) + 2 * φ.length + 3)
      ⟨some .a0, v, (initMS φ o).stk⟩ ⟨some .h0, v', (diaMS φ o).stk⟩ := by
  have hT := Check.toks_reverse φ
  have hL : (φ.reverse.flatMap Check.clRev).length = (toks φ).length := by
    rw [← hT, List.length_reverse]
  obtain ⟨v₁, r₁⟩ := aformula_run (toks φ).length φ [] (Or.inl rfl) [] (initMS φ o) v
    (by simp [initMS, hT]) rfl rfl rfl (by simp [vstk, hL])
  rw [hL] at r₁
  set s₁ : MS := { initMS φ o with
    t := [], f := toks φ ++ (initMS φ o).f, v := vstk ((varsOf φ).foldr insV []),
    c := (initMS φ o).c + φ.length, mm := (initMS φ o).mm + 3 * φ.length } with hs₁
  have r₂ := a0_nil s₁ v₁ rfl
  obtain ⟨v₃, r₃⟩ := cp_run (a := .C) (c := .P) Sym.cl Sym.cl (by decide) (by decide) (by decide)
    (l₁ := .b0) (l₂ := .b1) (next := .h0) rfl rfl φ.length true s₁.stk (by simp [s₁, initMS])
    rfl
  have e : update s₁.stk .P (cnt Sym.cl φ.length ++ s₁.stk .P) = (diaMS φ o).stk := by
    have : cnt Sym.cl φ.length ++ s₁.stk .P = cnt Sym.cl φ.length := by simp [s₁, initMS]
    rw [this, upd_P]
    simp [s₁, initMS, diaMS, hamVars_eq]
  rw [e] at r₃
  exact ⟨v₃, runLe_cast (r₁.trans ((r₂.trans r₃).le le_rfl)) (by omega) rfl⟩

end Cslib.Complexity.Karp.EmitHam
