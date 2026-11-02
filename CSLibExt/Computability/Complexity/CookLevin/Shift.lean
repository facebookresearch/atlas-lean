/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Copyright 2026 Joshua Tan.
Authors: Joshua Tan (original development); ported by Adam Kiezun and Metamate.

Adapted from `D3Shift.lean` of `JoshuaTan42/millennium-cook-levin` at commit
`879c4835640119ad009abeb62ebd7a96f87eb9e8`
(<https://github.com/JoshuaTan42/millennium-cook-levin/blob/879c4835640119ad009abeb62ebd7a96f87eb9e8/D3Shift.lean>),
licensed under the Apache License, Version 2.0
(<https://www.apache.org/licenses/LICENSE-2.0>). Changes: module-system header and imports,
`Cslib.Complexity.CookLevin` namespaces, deprecated lemma
names updated, manual `Fintype` instances for enumeration types (`deriving Fintype` fails on them at
the pinned Mathlib); module docstring rewritten for this repository (the source's notes and status
lines dropped), missing docstrings added, long lines wrapped.
-/

module

public import CSLibExt.Computability.Complexity.CookLevin.OneHot

/-!
# Cook-Levin: generator machine for the cell-shift family

The stack contents of the verifier are a table of cells `C[t, k, j, x]` (time `t`, stack `k`, depth
`j`, symbol code `x`). With a situation variable `S[t, i]` for situation `i` at time `t`, and for
`t < T`, `i < N`, `k < KK`, `p = pl i k` (symbols pushed and still on top), `c = cn i k` (original
symbols consumed), `m = max p c`, the family is:
* in-range shifts, `u < H − m`, `x < g`: `¬C[t,k,u+c,x] ∨ ¬S[t,i] ∨ C[t+1,k,u+p,x]`;
* overflow fill (`c > p`), `r < c − p`: `¬S[t,i] ∨ C[t+1,k,H−c+p+r,0]` (code `0` is the empty
  cell);
* pushed fill, `j < p`: `¬S[t,i] ∨ C[t+1,k,j,pu i k j]` (`pu i k j` codes the pushed symbol at
  depth `j`).

Each clause is dense over all `V = (T+1)·W` variables. `shFamily` is the family, `prog` the
counter machine emitting it, and `sh_time` its run with a polynomial step bound. `T` and
`H` are runtime inputs in unary; the `t`, `u`, `r` loops run at run time, while `i`, `k`, `x` and
the pushed-fill `j` are label chains.
-/

@[expose] public section


namespace Cslib.Complexity.CookLevin.Shift

open MetaMathlibExt

open MetaMathlibExt.TM2Program Cslib.Complexity.DenseSAT Turing Function
open Cslib.Complexity.CookLevin.Family (Layout gapEnc Inc Inc.le encodeClause_denseClause gapEnc_shift inc_of_mono denseClause cIdx_lt_next_row)
open Cslib.Complexity.CookLevin.CounterView (MS SK SΓ st st_c st_out update_st_c emitS emitOut incS
  drainS xferES copyS mulS mulS_run gapS bud_st stLoop)

/-! ## [LIB] Decrement in the counter view -/

theorem decS {C Λ : Type} [DecidableEq C] {M : Λ → TM2.Stmt (SΓ C) Λ Bool} {self ifZero ifPos : Λ}
    {x : C} (hp : M self = decr (.c x) ifZero ifPos) (F : C → ℕ) (n : ℕ) (hF : F x = n + 1)
    (v : Bool) (o : List Bool) :
    Run M 1 ⟨some self, v, st F o⟩ ⟨some ifPos, true, st (update F x n) o⟩ := by
  have := decr_run_cnt hp v (S := st F o) (u := ()) (n := n) (by simp [hF])
  rw [update_st_c] at this
  exact this

/-! ## [FAM] The family (pure specification) -/

section Spec

variable (L : Layout) (sa : ℕ → ℕ) (pl cn : ℕ → ℕ → ℕ) (pu : ℕ → ℕ → ℕ → ℕ)

/-- **Literals of an in-range shift clause.** Fix a layout $L$ and tables $\mathrm{sa}$,
$\mathrm{pl}$, $\mathrm{cn}$. For a height $H$, write $C[t,k,j,x]$ for the cell variable of
stack $k$, depth $j$ and symbol code $x$ at time $t$, and $X[t,a]$ for the label/state variable
$a$ at time $t$. With $c = \mathrm{cn}(i,k)$ and $p = \mathrm{pl}(i,k)$, the literals of the
clause $(t, i, k, u, x)$ are, as (variable, sign) pairs in this order, $\neg C[t,k,u+c,x]$,
$\neg X[t+1,\mathrm{sa}(i)]$ and $C[t+1,k,u+p,x]$. Writing $S[t,i] = X[t+1,\mathrm{sa}(i)]$ for
the situation variable of situation $i$ at time $t$, this is the clause
$\neg C[t,k,u+c,x] \lor \neg S[t,i] \lor C[t+1,k,u+p,x]$.

When all indices are in range, the literals are in increasing variable order: a row $t$ cell, the
label/state block of row $t+1$, then a row $t+1$ cell. -/
def shLits (H t i k u x : ℕ) : List (ℕ × Bool) :=
  [(L.cIdx H t k (u + cn i k) x, false), (L.xIdx H (t + 1) (sa i), false),
    (L.cIdx H (t + 1) k (u + pl i k) x, true)]

/-- **Literals of an overflow clause.** For a layout $L$ with label block size $A$, $K$ stacks and
$g$ symbol codes, row width $W = A + K H g$, situation offsets $s_a$, push counts $p$, consumed
counts $c$ and numbers $H, t, i, k, r$, write $S[t, i] = (t + 1) W + s_a(i)$ for the situation
variable (the label/state variable $s_a(i)$ of row $t + 1$), and
$C[t', k', j, x] = t' W + A + (k' H + j) g + x$ for the cell variable of row $t'$, stack $k'$,
depth $j$ and symbol code $x$. The overflow clause $(t, i, k, r)$ is the list of two (variable,
sign) literals $\neg S[t, i] \lor C[t + 1, k, H - c(i, k) + p(i, k) + r, 0]$: first the negated
situation variable $S[t, i]$, then the positive cell variable of row $t + 1$, stack $k$, depth
$H - c(i, k) + p(i, k) + r$ and symbol code $0$ (the empty cell). Subtraction is truncated at
zero. -/
def ovLits (H t i k r : ℕ) : List (ℕ × Bool) :=
  [(L.xIdx H (t + 1) (sa i), false), (L.cIdx H (t + 1) k (H - cn i k + pl i k + r) 0, true)]

/-- **Literals of a pushed-fill clause.** For a layout $L$ with label block size $A$, $K$ stacks
and $g$ symbol codes, row width $W = A + K H g$, situation offsets $s_a$, pushed codes $p_u$ and
numbers $H, t, i, k, j$, write $S[t, i] = (t + 1) W + s_a(i)$ for the situation variable (the
label/state variable $s_a(i)$ of row $t + 1$), and
$C[t', k', j', x] = t' W + A + (k' H + j') g + x$ for the cell variable of row $t'$, stack $k'$,
depth $j'$ and symbol code $x$. The pushed-fill clause $(t, i, k, j)$ is the list of two
(variable, sign) literals $\neg S[t, i] \lor C[t + 1, k, j, p_u(i, k, j)]$: first the negated
situation variable $S[t, i]$, then the positive cell variable of row $t + 1$, stack $k$, depth
$j$ and symbol code $p_u(i, k, j)$. It is used for depths $j$ below the number of symbols that
situation $i$ pushes on stack $k$. -/
def pfLits (H t i k j : ℕ) : List (ℕ × Bool) :=
  [(L.xIdx H (t + 1) (sa i), false), (L.cIdx H (t + 1) k j (pu i k j), true)]

/-- **The shift block of a situation and a stack.** Fix a layout with $A$ label variables, $K$
stacks and $g$ symbol codes, the generator's parameters $sa$, $pl$, $cn$, $pu$, and
$T, H, t, i, k \in \mathbb{N}$. Write $p = pl(i, k)$, $c = cn(i, k)$, $W = A + K H g$ for the row
width and $V = (T + 1) W$ for the number of variables. The block is the CNF formula consisting, in
this order, of: for each $u < H - \max(p, c)$ and each $x < g$ (ordered by $u$, then $x$), the
dense clause over $V$ variables with the in-range shift literals for $(t, i, k, u, x)$; for each
$r < c - p$, the dense clause over $V$ variables with the overflow literals for $(t, i, k, r)$;
and for each $j < p$, the dense clause over $V$ variables with the pushed-fill literals for
$(t, i, k, j)$. Subtraction is truncated at $0$. -/
def shBlk (T H t i k : ℕ) : CNF :=
  ((List.range (H - max (pl i k) (cn i k))).flatMap fun u =>
      (List.range L.g).map fun x => denseClause (L.numVars T H) (shLits L sa pl cn H t i k u x)) ++
    ((List.range (cn i k - pl i k)).map fun r =>
      denseClause (L.numVars T H) (ovLits L sa pl cn H t i k r)) ++
    (List.range (pl i k)).map fun j => denseClause (L.numVars T H) (pfLits L sa pu H t i k j)

/-- **The cell-shift clause family.** Fix a layout $L$ with $K$ stacks and situation tables
$\mathrm{sa}$, $\mathrm{pl}$, $\mathrm{cn}$, $\mathrm{pu}$. For $N, T, H \in \mathbb{N}$, the
shift family is the CNF formula obtained by concatenating the shift blocks of situation $i$ and
stack $k$ at time $t$ for all $t < T$, $i < N$ and $k < K$, ordered lexicographically by
$(t, i, k)$. -/
def shFamily (N T H : ℕ) : CNF :=
  (List.range T).flatMap fun t => (List.range N).flatMap fun i =>
    (List.range L.KK).flatMap fun k => shBlk L sa pl cn pu T H t i k

/-- **Well-formed situation tables for the cell-shift family.** Given a layout with label/state
block size $A$, $K$ stacks, $g$ symbol codes and window depth $d$, a situation-offset table
$\mathrm{sa}$, push-count and consumed-count tables $\mathrm{pl}$ and $\mathrm{cn}$ and a
pushed-code table $\mathrm{pu}$, the tables are well formed for $N$ situations at height $H$ when
$g > 0$, $d \le H$, $\mathrm{sa}(i) < A$ for every $i < N$, and for all $i < N$ and $k < K$:
$\mathrm{pl}(i, k) \le d$, $\mathrm{cn}(i, k) \le d$, and $\mathrm{pu}(i, k, j) < g$ for every
$j < \mathrm{pl}(i, k)$. -/
structure WF (N H : ℕ) : Prop where
  g_pos : 0 < L.g
  d_le : L.d ≤ H
  sa_lt : ∀ i < N, sa i < L.A
  pl_le : ∀ i < N, ∀ k < L.KK, pl i k ≤ L.d
  cn_le : ∀ i < N, ∀ k < L.KK, cn i k ≤ L.d
  pu_lt : ∀ i < N, ∀ k < L.KK, ∀ j < pl i k, pu i k j < L.g

/-- **Coverage of target depths.** Let $p, c, H$ be natural numbers with $p \le H$ and $c \le H$,
and let $m = \max(p, c)$. Every natural number $j < H$ satisfies $j < p$, or $j = u + p$ for some
natural number $u < H - m$, or $j = H - c + p + r$ for some natural number $r < c - p$, where
$c - p$ is truncated subtraction (zero when $c \le p$).

In the cell-shift family these are the pushed-fill, in-range and overflow target depths of a
stack in the row after a time step. -/
theorem depth_cover {p c H : ℕ} (hp : p ≤ H) (hc : c ≤ H) (j : ℕ) (hj : j < H) :
    j < p ∨ (∃ u < H - max p c, j = u + p) ∨ (∃ r < c - p, j = H - c + p + r) := by
  by_cases h1 : j < p
  · exact Or.inl h1
  by_cases h2 : j < H - max p c + p
  · exact Or.inr (Or.inl ⟨j - p, by omega, by omega⟩)
  · exact Or.inr (Or.inr ⟨j - (H - c + p), by omega, by omega⟩)

/-- **Bounds on in-range and overflow target depths.** Let $p, c, H$ be natural numbers with
$p \le H$ and $c \le H$, and let $m = \max(p, c)$. For every natural number $u < H - m$ we have
$p \le u + p$, $u + p < H - c + p$ and $u + p < H$. For every natural number $r < c - p$, where
$c - p$ is truncated subtraction, we have $H - m + p = H - c + p$ and $H - c + p + r < H$. -/
theorem depth_disjoint {p c H : ℕ} (hp : p ≤ H) (hc : c ≤ H) :
    (∀ u < H - max p c, p ≤ u + p ∧ u + p < H - c + p ∧ u + p < H) ∧
    (∀ r < c - p, H - max p c + p = H - c + p ∧ H - c + p + r < H) := by
  constructor <;> intro _ _ <;> omega

end Spec

/-! ## [FAM] The generator machine -/

/-- **Counters of the cell-shift generator.** The type with 23 elements, one for each unit counter
of the counter machine that emits the cell-shift clause family: $\mathrm{Tn}$, $\mathrm{Ti}$,
$\mathrm{Hs}$, $\mathrm{Gc}$, $\mathrm{HG}$, $\mathrm{Wc}$, $\mathrm{Vc}$, $\mathrm{TW}$,
$\mathrm{TW1}$, $\mathrm{KB}$, $\mathrm{U}$, $\mathrm{Ui}$, $\mathrm{R}$, $\mathrm{Ri}$,
$\mathrm{CB}$, $\mathrm{CW}$, $\mathrm{P}$, $\mathrm{Q}$, $\mathrm{tmp}$, $\mathrm{md}$,
$\mathrm{Ka}$, $\mathrm{c1}$ and $\mathrm{c2}$. -/
inductive CK
  | Tn | Ti | Hs | Gc | HG | Wc | Vc | TW | TW1 | KB | U | Ui | R | Ri | CB | CW | P | Q | tmp | md | Ka
  | c1 | c2
  deriving DecidableEq
instance CK.instFintypeEnumFix : Fintype CK where
  elems := ⟨↑[CK.Tn, CK.Ti, CK.Hs, CK.Gc, CK.HG, CK.Wc, CK.Vc, CK.TW, CK.TW1, CK.KB, CK.U, CK.Ui,
      CK.R, CK.Ri, CK.CB, CK.CW, CK.P, CK.Q, CK.tmp, CK.md, CK.Ka, CK.c1, CK.c2], by decide⟩
  complete := fun x => by cases x <;> decide

/-- **Base counters of literal positions.** The three bases $s$, $cb$ and $cw$ from which a literal
position is computed; at time step $t$, with $W$ the row width, $s$ stands for the counter
$TW1 = (t + 1) \cdot W$ and serves the situation variable. -/
inductive BS | s | cb | cw
  deriving DecidableEq
instance BS.instFintypeEnumFix : Fintype BS where
  elems := ⟨↑[BS.s, BS.cb, BS.cw], by decide⟩
  complete := fun x => by cases x <;> decide

/-- **Counter holding a literal base.** The map from the three kinds of literal base to
counters of the generator. With $t$ the current time step and $W$ the number of variables per
time step, the situation base goes to the counter holding $(t + 1) W$, the start of row
$t + 1$; the current-row cell base goes to the cell-base counter; and the next-row cell base
goes to the counter holding the cell base plus $W$. -/
def BS.k : BS → CK
  | .s => .TW1
  | .cb => .CB
  | .cw => .CW

/-- **Clause kinds of the cell-shift family.** For natural numbers $g$ and $d$, a clause kind is
either an in-range shift clause $\mathrm{sh}(x)$ for a symbol code $x < g$, the overflow-fill
clause $\mathrm{ov}$, or a pushed-fill clause $\mathrm{pf}(j)$ for a pushed depth $j < d$. These
are the kinds of clause in the block of a situation $i$ and a stack $k$. -/
inductive CL (g d : ℕ)
  | sh (x : Fin g)
  | ov
  | pf (j : Fin d)
  deriving DecidableEq, Fintype

namespace CL

variable {g d : ℕ}

/-- **Number of literals of a cell-shift clause kind.** An in-range shift clause has $3$
literals, and an overflow clause and a pushed-fill clause have $2$ each. -/
def nl : CL g d → ℕ
  | sh _ => 3
  | ov => 2
  | pf _ => 2

/-- **Base counter of a literal.** For a clause kind $c$ and $l \in \mathbb{N}$: if $c$ is an
in-range shift clause, literal $l$ has base $cb$ when $l = 0$, $s$ when $l = 1$ and $cw$ when
$l \ge 2$; if $c$ is an overflow or pushed-fill clause, it has base $s$ when $l = 0$ and $cw$
otherwise. -/
def bs : CL g d → ℕ → BS
  | sh _, l => if l = 0 then .cb else if l = 1 then .s else .cw
  | ov, l => if l = 0 then .s else .cw
  | pf _, l => if l = 0 then .s else .cw

/-- **Constant offsets of the literals of a clause kind.** Let $g$ be the number of symbol codes
of the clause kinds, and let $s, p, c \in \mathbb{N}$ and $q : \mathbb{N} \to \mathbb{N}$
(situation offset, push count, consumed count and pushed codes). The constant offset of literal
$l$ is: for an in-range shift clause $\mathrm{sh}(x)$, $cg + x$ if $l = 0$, $s$ if $l = 1$ and
$pg + x$ otherwise; for the overflow-fill clause $\mathrm{ov}$, $s$ if $l = 0$ and $pg$
otherwise; for a pushed-fill clause $\mathrm{pf}(j)$, $s$ if $l = 0$ and $jg + q(j)$
otherwise. -/
def cs (s p c : ℕ) (q : ℕ → ℕ) : CL g d → ℕ → ℕ
  | sh x, l => if l = 0 then c * g + x else if l = 1 then s else p * g + x
  | ov, l => if l = 0 then s else p * g
  | pf j, l => if l = 0 then s else j.val * g + q j.val

/-- **Literal signs of a shift clause kind.** For a clause kind $c$ of a cell-shift block and
$l \in \mathbb{N}$, the sign of literal $l$ of $c$ is positive exactly when $l + 1$ equals the
number of literals of $c$; so only the last literal is positive. -/
def sg (cl : CL g d) (l : ℕ) : Bool := decide (l + 1 = cl.nl)

theorem nl_le (cl : CL g d) : cl.nl ≤ 3 := by cases cl <;> simp [nl]

end CL

/-- **Precomputation stages of the shift generator.** The labels of the precomputation that the
cell-shift generator runs before its time loop: six plain stages and three multiplication sites,
each of the latter tagged with a stage of the multiplication routine. For a layout with $A$ label
variables, $K$ stacks and $g$ symbol codes, and the inputs $T$ (number of time steps) and $H$
(height), in order of execution they set a counter $G$ to $g$; set a counter $HG$ to $H g$ (a
multiplication site); set the row-width counter $W$ to $A$; set a scratch counter to $K$; add
$K \cdot HG$ to $W$ (a multiplication site), so that $W = A + K H g$; empty the scratch counter;
set the variable counter $V$ to $T W$ (a multiplication site); and add $W$ to $V$ in two copy
steps, so that $V = (T + 1) W$. -/
inductive PS
  | eg | hg (s : MS) | ew | ek | w (s : MS) | dk | v (s : MS) | vw1 | vw2
  deriving DecidableEq, Fintype

/-- **Stages of the cell-shift literal routine.** The routine emitting one literal has fifteen
stages: two copy stages, an offset stage, a decrement stage, a compare stage, two restore stages
for each comparison outcome (less, equal, greater), an absent-slot emission stage, a failure
stage, a slot emission stage and a drain stage. -/
inductive LS
  | cp1 | cp2 | eo | dec | cmp | r (o : Ordering) | rB (o : Ordering) | emL | bad | slot | dq
  deriving DecidableEq, Fintype

/-- **Setup and loop stages of a cell-shift block.** The finite type of stages of the setup and
loops of an $(i, k)$ block of the cell-shift generator: the base stages $\mathrm{kbE}$,
$\mathrm{kbC1}$, $\mathrm{kbC2}$, $\mathrm{kbK}$, $\mathrm{kbM}(s)$ for each stage $s$ of the
multiplication routine, $\mathrm{kbD}$, $\mathrm{uC1}$ and $\mathrm{uC2}$; the overflow-loop
stages $\mathrm{oE}$, $\mathrm{oHead}$, $\mathrm{oRest}$, $\mathrm{oC1}$, $\mathrm{oC2}$,
$\mathrm{oR1}$, $\mathrm{oR2}$, $\mathrm{oM}(s)$ for each stage $s$ of the multiplication routine,
and $\mathrm{oD}$; the in-range-loop and drain stages $\mathrm{sHead}$, $\mathrm{sRest}$,
$\mathrm{dU}$, $\mathrm{dR}$ and $\mathrm{dKB}$; and the pushed-fill stages $\mathrm{fC1}$,
$\mathrm{fC2}$, $\mathrm{fW1}$, $\mathrm{fW2}$ and $\mathrm{fD1}$. -/
inductive ST
  | kbE | kbC1 | kbC2 | kbK | kbM (s : MS) | kbD | uC1 | uC2
  | oE | oHead | oRest | oC1 | oC2 | oR1 | oR2 | oM (s : MS) | oD
  | sHead | sRest | dU | dR | dKB
  | fC1 | fC2 | fW1 | fW2 | fD1
  deriving DecidableEq, Fintype

/-- **Loop-body stages of the cell-shift generator.** For a symbol count $g$ and a window depth
$d$, the finite type of stages of the loop body of an $(i, k)$ block: for each flag $b$, two
stages adding the block base, four stages building the second base and two drain stages; one
stage for each stage of the multiplication routine; and for each clause kind $c$ (over $g$ and
$d$), a terminator stage, two stages loading the variable count, one stage for each literal
position $l < 3$ and each stage of the literal routine, and a finishing stage. The flag $b$ is
true in the in-range loop and false in the overflow loop. -/
inductive BD (g d : ℕ)
  | bC1 (b : Bool) | bC2 (b : Bool) | sM (s : MS)
  | w1 (b : Bool) | w2 (b : Bool) | w3 (b : Bool) | w4 (b : Bool)
  | e00 (c : CL g d) | cv1 (c : CL g d) | cv2 (c : CL g d) | lit (c : CL g d) (l : Fin 3) (s : LS)
  | fin (c : CL g d)
  | dCB (b : Bool) | dCW (b : Bool)
  deriving DecidableEq, Fintype

/-- **Labels of the cell-shift generator.** For natural numbers $N$, $K$, $g$ and $d$, a label is
one of: a precomputation stage $\mathrm{pre}(s)$; a time-loop label $\mathrm{tHead}$,
$\mathrm{tRest}$, $\mathrm{tw}(s)$ for a multiplication stage $s$, $\mathrm{t1a}$,
$\mathrm{t1b}$, $\mathrm{t1c}$, $\mathrm{t1d}$, $\mathrm{tEnd}$ or $\mathrm{tEnd2}$; a setup or
loop stage $\mathrm{s}(i, k, x)$ of the block of situation $i < N$ and stack $k < K$; a decrement
step $\mathrm{sb}(i, k, r)$ with $r < d + 1$; a loop-body stage $\mathrm{b}(i, k, x)$ of that
block, over clause kinds with parameters $g$ and $d$; or a halting label $\mathrm{bad}$ or
$\mathrm{done}$. -/
inductive GL (N KK g d : ℕ)
  | pre (s : PS)
  | tHead | tRest | tw (s : MS) | t1a | t1b | t1c | t1d | tEnd | tEnd2
  | s (i : Fin N) (k : Fin KK) (x : ST)
  | sb (i : Fin N) (k : Fin KK) (r : Fin (d + 1))
  | b (i : Fin N) (k : Fin KK) (x : BD g d)
  | bad | done
  deriving DecidableEq, Fintype

namespace GL

variable {N KK g d : ℕ}

/-- **Entry label of a literal routine of the cell-shift generator.** For a situation $i < N$, a
stack $k < K$, a clause kind $c$ and $l \in \mathbb{N}$, the entry label of literal $l$ is the
first stage of the routine emitting literal $l$ of a clause of kind $c$ in block $(i, k)$ when
$l < 3$, and the generator's final label when $l \ge 3$ (that case is never used). -/
def litL (i : Fin N) (k : Fin KK) (c : CL g d) (l : ℕ) : GL N KK g d :=
  if h : l < 3 then .b i k (.lit c ⟨l, h⟩ .cp1) else .done

/-- **Label after a literal routine.** For block $(i, k)$ of the cell-shift generator, a clause
kind $c$ and $l \in \mathbb{N}$, with the literals of a clause emitted from the last down to the
first: the label is the finishing stage of clause $c$ in block $(i, k)$ when $l = 0$; otherwise it
is the first stage of the routine for literal $l - 1$ of $c$ in block $(i, k)$ when $l - 1 < 3$,
and the final label $\mathrm{done}$, at which the generator halts, otherwise. -/
def after (i : Fin N) (k : Fin KK) (c : CL g d) (l : ℕ) : GL N KK g d :=
  if l = 0 then .b i k (.fin c) else litL i k c (l - 1)

/-- **Entry label of the in-range chain.** For a situation $i < N$, a stack $k < K$ and a number
$n$, the label of the generator with $N$ situations, $K$ stacks, $g$ symbol codes and window
depth $d$ from which the in-range shift clauses for the symbol codes $x < n$ of the current cell
pair of block $(i, k)$ are emitted before the in-range drains: the in-range drain stage
$\mathrm{dCB}$ of block $(i, k)$ if $n = 0$, the first stage of the routine emitting the in-range
shift clause for symbol code $n - 1$ of block $(i, k)$ if $1 \le n \le g$, and the halting label
$\mathrm{done}$ (unused) if $n > g$. -/
def xFrom (i : Fin N) (k : Fin KK) (n : ℕ) : GL N KK g d :=
  if n = 0 then .b i k (.dCB true) else if h : n - 1 < g then .b i k (.e00 (.sh ⟨n - 1, h⟩))
  else .done

/-- **Entry label of the pushed-fill chain.** For a situation $i < N$, a stack $k < K$ and a
number $n$, the label of the generator with $N$ situations, $K$ stacks, $g$ symbol codes and
window depth $d$ from which the pushed-fill clauses $j < n$ of block $(i, k)$ are emitted before
the fill drains: the fill-drain stage $\mathrm{fD1}$ of block $(i, k)$ if $n = 0$, the first
stage of the routine emitting pushed-fill clause $n - 1$ of block $(i, k)$ if $1 \le n \le d$,
and the halting label $\mathrm{done}$ (unused) if $n > d$. -/
def pfFrom (i : Fin N) (k : Fin KK) (n : ℕ) : GL N KK g d :=
  if n = 0 then .s i k .fD1 else if h : n - 1 < d then .b i k (.e00 (.pf ⟨n - 1, h⟩)) else .done

/-- **Label after a clause of the cell-shift generator.** For a situation $i < N$ and a stack
$k < K$, in block $(i, k)$: after the in-range clause for symbol $x$ the generator goes to the
start of the in-range clause for symbol $x - 1$, or to the in-range drains when $x = 0$; after
the overflow clause it goes to the overflow drains; after the pushed-fill clause for depth $j$
it goes to the start of the pushed-fill clause for depth $j - 1$, or to the pushed-fill drains
when $j = 0$. -/
def nextC (i : Fin N) (k : Fin KK) : CL g d → GL N KK g d
  | .sh x => xFrom i k x.val
  | .ov => .b i k (.dCB false)
  | .pf j => pfFrom i k j.val

/-- **Label of the decrement chain.** Among the generator labels for $N$ situations, $K$ stacks,
$g$ symbol codes and window depth $d$, take a situation $i < N$, a stack $k < K$ and
$n \in \mathbb{N}$. The label is the pushed-fill setup label of block $(i, k)$ if $n = 0$, the
decrement label of block $(i, k)$ with index $n - 1$ if $1 \le n \le d + 1$, and the terminal
label otherwise. It marks the point where $n$ decrements of the counter $U$ remain before the
pushed-fill setup. -/
def sbL (i : Fin N) (k : Fin KK) (n : ℕ) : GL N KK g d :=
  if n = 0 then .s i k .fC1 else if h : n - 1 < d + 1 then .sb i k ⟨n - 1, h⟩ else .done

/-- **Entry label of the situation chain.** For a natural number $n$, with $N$ the number of
situations and $K$ the number of stacks, this is the end-of-time-step label when $n = 0$ or
$K = 0$; the first setup stage of block $(n - 1, K - 1)$ when $1 \le n \le N$ and $K \ge 1$;
and the terminal (halting) label when $n > N$ and $K \ge 1$. For $n \le N$ it is the label
from which the generator emits the blocks of situations $i < n$ and then ends the time step. -/
def iFrom (n : ℕ) : GL N KK g d :=
  if n = 0 then .tEnd
  else if h : n - 1 < N ∧ 0 < KK then .s ⟨n - 1, h.1⟩ ⟨KK - 1, by omega⟩ .kbE
  else if KK = 0 then .tEnd else .done

/-- **Entry label of the stack chain of a situation.** For natural numbers $i$ and $n$, with $N$
the number of situations and $K$ the number of stacks, this is the entry label of the situation
chain for $i$ when $n = 0$; the first setup stage of block $(i, n - 1)$ when $1 \le n \le K$ and
$i < N$; and the terminal (halting) label otherwise. For $i < N$ and $n \le K$ it is the label
from which the generator emits the blocks of stacks $k < n$ of situation $i$ and then the blocks
of situations $< i$. -/
def ik (i n : ℕ) : GL N KK g d :=
  if n = 0 then iFrom i else if h : i < N ∧ n - 1 < KK then .s ⟨i, h.1⟩ ⟨n - 1, h.2⟩ .kbE
  else .done

theorem litL_of_lt {i : Fin N} {k : Fin KK} {c : CL g d} {l : ℕ} (h : l < 3) :
    (litL i k c l : GL N KK g d) = .b i k (.lit c ⟨l, h⟩ .cp1) := dite_eq_left h

theorem xFrom_succ {i : Fin N} {k : Fin KK} {n : ℕ} (h : n < g) :
    (xFrom i k (n + 1) : GL N KK g d) = .b i k (.e00 (.sh ⟨n, h⟩)) := by
  simp [xFrom, h]

theorem pfFrom_succ {i : Fin N} {k : Fin KK} {n : ℕ} (h : n < d) :
    (pfFrom i k (n + 1) : GL N KK g d) = .b i k (.e00 (.pf ⟨n, h⟩)) := by
  simp [pfFrom, h]

theorem sbL_succ {i : Fin N} {k : Fin KK} {n : ℕ} (h : n < d + 1) :
    (sbL i k (n + 1) : GL N KK g d) = .sb i k ⟨n, h⟩ := by
  simp [sbL, h]

theorem ik_succ {i n : ℕ} (hi : i < N) (hn : n < KK) :
    (ik i (n + 1) : GL N KK g d) = .s ⟨i, hi⟩ ⟨n, hn⟩ .kbE := by
  simp [ik, hi, hn]

theorem iFrom_succ {n : ℕ} (hn : n < N) (hK : 0 < KK) :
    (iFrom (n + 1) : GL N KK g d) = ik n KK := by
  have h1 : KK - 1 < KK := by omega
  simp [iFrom, ik, hn, hK, h1, hK.ne']

theorem iFrom_KK0 (hK : KK = 0) (n : ℕ) : (iFrom n : GL N KK g d) = .tEnd := by
  unfold iFrom; split_ifs <;> first | rfl | omega

end GL

section Machine

variable (L : Layout) (sa : ℕ → ℕ) (pl cn : ℕ → ℕ → ℕ) (pu : ℕ → ℕ → ℕ → ℕ) (N : ℕ)

/-- **Labels of the shift generator.** For a layout with $K$ stacks, $g$ symbol codes and
window depth $d$, and a number $N$ of situations, the labels of the generator are the finite
label type with parameters $N$, $K$, $g$ and $d$. -/
abbrev Lab := GL N L.KK L.g L.d

/-- **Constant offset of a literal in a block.** Let $L$ be a layout with $K$ stacks, $g$ symbol
codes and window depth $d$, let $N \in \mathbb{N}$ be the number of situations, and let
$\mathrm{sa}$, $\mathrm{pl}$, $\mathrm{cn}$ and $\mathrm{pu}$ give the situation offsets, push
counts, consumed counts and pushed codes. For a situation $i < N$, a stack $k < K$, a clause kind
$c$ with parameters $g$ and $d$, and $l \in \mathbb{N}$, the constant offset of literal $l$ of $c$
in block $(i, k)$ is the constant offset of literal $l$ of $c$ with situation offset
$\mathrm{sa}(i)$, push count $\mathrm{pl}(i, k)$, consumed count $\mathrm{cn}(i, k)$ and pushed
codes $j \mapsto \mathrm{pu}(i, k, j)$. -/
def csv (i : Fin N) (k : Fin L.KK) (c : CL L.g L.d) (l : ℕ) : ℕ :=
  c.cs (sa i) (pl i k) (cn i k) (pu i k) l

/-- **Literal routine of the cell-shift generator.** For a situation $i < N$, a stack $k < K$, a
clause kind $c$ and a literal index $l < 3$, this is the program fragment, indexed by the stages
of the literal routine, that emits literal $l$ of clause $c$ in block $(i, k)$. Write $B$ for the
base counter of literal $l$ and $a$ for its constant offset in block $(i, k)$. Started with $Q$
and the scratch counters empty, the routine copies the value $b$ of $B$ into the counter $Q$
through a scratch counter, restoring $B$, and adds $a$, so that $Q = b + a$. It then repeats:
decrement the counter $P$, halting if $P$ is already $0$; compare $P$ with $Q$ through two
scratch counters, restoring both; if they differ, push the absent-slot code $01$ onto the output
and repeat; if they are equal, push the slot code of a literal whose sign is positive exactly
when $l$ is the last literal of $c$. Finally it empties $Q$ and jumps to the routine of literal
$l - 1$, or to the end of the clause when $l = 0$. -/
def litP (i : Fin N) (k : Fin L.KK) (c : CL L.g L.d) (l : Fin 3) :
    LS → TM2.Stmt (SΓ CK) (Lab L N) Bool
  | .cp1 => xfer (.c (c.bs l).k) [⟨.c .Q, ()⟩, ⟨.c .tmp, ()⟩] (.b i k (.lit c l .cp1))
      (.b i k (.lit c l .cp2))
  | .cp2 => xfer (.c .tmp) [⟨.c (c.bs l).k, ()⟩] (.b i k (.lit c l .cp2)) (.b i k (.lit c l .eo))
  | .eo => emitR (.c .Q) (List.replicate (csv L sa pl cn pu N i k c l) ()) (.b i k (.lit c l .dec))
  | .dec => decr (.c .P) (.b i k (.lit c l .bad)) (.b i k (.lit c l .cmp))
  | .cmp => cmpStep (.c .P) (.c .Q) (.c .c1) (.c .c2) () () (.b i k (.lit c l .cmp))
      (.b i k (.lit c l (.r .lt))) (.b i k (.lit c l (.r .eq))) (.b i k (.lit c l (.r .gt)))
  | .r o => xfer (.c .c1) [⟨.c .P, ()⟩] (.b i k (.lit c l (.r o))) (.b i k (.lit c l (.rB o)))
  | .rB o => xfer (.c .c2) [⟨.c .Q, ()⟩] (.b i k (.lit c l (.rB o)))
      (if o = .eq then .b i k (.lit c l .slot) else .b i k (.lit c l .emL))
  | .emL => emitR .out [false, true] (.b i k (.lit c l .dec))
  | .bad => .halt
  | .slot => emitR .out (encodeSlot (some (c.sg l))) (.b i k (.lit c l .dq))
  | .dq => xfer (.c .Q) [] (.b i k (.lit c l .dq)) (GL.after i k c l)

/-- **Block stages of the cell-shift generator.** For a layout $L$ with label block size $A$ and
$K$ stacks, push-count and consumed-count tables $\mathrm{pl}$ and $\mathrm{cn}$, a number $N$ of
situations, a situation $i < N$ and a stack $k < K$, write $p = \mathrm{pl}(i, k)$ and
$c = \mathrm{cn}(i, k)$.
This assigns a statement of the generator to each setup or loop stage of block $(i, k)$; below,
"add $X$ to $Y$" copies counter $X$ onto $Y$ through the scratch counter $\mathrm{tmp}$ in two
stages, restoring $X$, and "drain $X$" empties $X$. The setup pushes $A$ units onto $\mathrm{KB}$,
adds $\mathrm{TW}$ to $\mathrm{KB}$, pushes $k$ units onto $\mathrm{Ka}$, adds
$\mathrm{Ka} \cdot \mathrm{HG}$ to $\mathrm{KB}$ by the multiplication routine (index
$\mathrm{md}$, scratch $\mathrm{tmp}$), drains $\mathrm{Ka}$, adds $\mathrm{Hs}$ to $\mathrm{U}$,
and goes to the label of the decrement chain for $\max(p, c)$. The pushed-fill stages add
$\mathrm{KB}$ and then $\mathrm{Wc}$ to $\mathrm{CW}$ and go to the entry label of the pushed-fill
chain for $p$; the fill drain drains $\mathrm{CW}$, and the next stage pushes $c - p$ units onto
$\mathrm{R}$ (truncated subtraction). The overflow loop pops $\mathrm{R}$, pushing each unit on
the index counter $\mathrm{Ri}$; for each popped unit it adds $\mathrm{U}$ and then $\mathrm{R}$ to
$\mathrm{Ka}$, adds $\mathrm{Ka} \cdot \mathrm{Gc}$ to $\mathrm{CB}$ by the multiplication
routine, drains $\mathrm{Ka}$ and runs the loop body with flag false; when $\mathrm{R}$ is empty it
moves $\mathrm{Ri}$ back onto $\mathrm{R}$. The in-range loop likewise pops $\mathrm{U}$ onto
$\mathrm{Ui}$ and runs the loop body with flag true for each popped unit, and when $\mathrm{U}$ is
empty moves $\mathrm{Ui}$ back onto $\mathrm{U}$. Finally it drains $\mathrm{U}$, $\mathrm{R}$ and
$\mathrm{KB}$ and goes to the entry label of the stack chain of situation $i$ for $k$. -/
def stP (i : Fin N) (k : Fin L.KK) : ST → TM2.Stmt (SΓ CK) (Lab L N) Bool
  | .kbE => emitR (.c .KB) (List.replicate L.A ()) (.s i k .kbC1)
  | .kbC1 => xfer (.c .TW) [⟨.c .KB, ()⟩, ⟨.c .tmp, ()⟩] (.s i k .kbC1) (.s i k .kbC2)
  | .kbC2 => xfer (.c .tmp) [⟨.c .TW, ()⟩] (.s i k .kbC2) (.s i k .kbK)
  | .kbK => emitR (.c .Ka) (List.replicate k.val ()) (.s i k (.kbM .head))
  | .kbM s => mulS .Ka .md .HG .KB .tmp (fun s => .s i k (.kbM s)) (.s i k .kbD) s
  | .kbD => xfer (.c .Ka) [] (.s i k .kbD) (.s i k .uC1)
  | .uC1 => xfer (.c .Hs) [⟨.c .U, ()⟩, ⟨.c .tmp, ()⟩] (.s i k .uC1) (.s i k .uC2)
  | .uC2 => xfer (.c .tmp) [⟨.c .Hs, ()⟩] (.s i k .uC2) (GL.sbL i k (max (pl i k) (cn i k)))
  | .oE => emitR (.c .R) (List.replicate (cn i k - pl i k) ()) (.s i k .oHead)
  -- overflow loop over `r < c − p`: `CB := (U + r)·g`, then the shared body adds `KB`
  | .oHead => forHead (.c .R) (.c .Ri) () (.s i k .oC1) (.s i k .oRest)
  | .oRest => xfer (.c .Ri) [⟨.c .R, ()⟩] (.s i k .oRest) (.s i k .sHead)
  | .oC1 => xfer (.c .U) [⟨.c .Ka, ()⟩, ⟨.c .tmp, ()⟩] (.s i k .oC1) (.s i k .oC2)
  | .oC2 => xfer (.c .tmp) [⟨.c .U, ()⟩] (.s i k .oC2) (.s i k .oR1)
  | .oR1 => xfer (.c .R) [⟨.c .Ka, ()⟩, ⟨.c .tmp, ()⟩] (.s i k .oR1) (.s i k .oR2)
  | .oR2 => xfer (.c .tmp) [⟨.c .R, ()⟩] (.s i k .oR2) (.s i k (.oM .head))
  | .oM s => mulS .Ka .md .Gc .CB .tmp (fun s => .s i k (.oM s)) (.s i k .oD) s
  | .oD => xfer (.c .Ka) [] (.s i k .oD) (.b i k (.bC1 false))
  -- in-range loop over `u < H − m`
  | .sHead => forHead (.c .U) (.c .Ui) () (.b i k (.bC1 true)) (.s i k .sRest)
  | .sRest => xfer (.c .Ui) [⟨.c .U, ()⟩] (.s i k .sRest) (.s i k .dU)
  | .dU => xfer (.c .U) [] (.s i k .dU) (.s i k .dR)
  | .dR => xfer (.c .R) [] (.s i k .dR) (.s i k .dKB)
  | .dKB => xfer (.c .KB) [] (.s i k .dKB) (GL.ik i.val k.val)
  -- pushed fill: `CW := KB + W`, the chain `j < p`, drain
  | .fC1 => xfer (.c .KB) [⟨.c .CW, ()⟩, ⟨.c .tmp, ()⟩] (.s i k .fC1) (.s i k .fC2)
  | .fC2 => xfer (.c .tmp) [⟨.c .KB, ()⟩] (.s i k .fC2) (.s i k .fW1)
  | .fW1 => xfer (.c .Wc) [⟨.c .CW, ()⟩, ⟨.c .tmp, ()⟩] (.s i k .fW1) (.s i k .fW2)
  | .fW2 => xfer (.c .tmp) [⟨.c .Wc, ()⟩] (.s i k .fW2) (GL.pfFrom i k (pl i k))
  | .fD1 => xfer (.c .CW) [] (.s i k .fD1) (.s i k .oE)

/-- **Loop body of the cell-shift generator.** For a layout $L$ with $g$ symbol codes and a block
$(i, k)$, the generator's statement at each loop-body stage, with flag $b$ true in the in-range
loop and false in the overflow loop: add the counter $KB$ to the counter $CB$; when $b$ is true,
add the product of the counters $U$ and $Gc$ to $CB$; add $CB$ and then the counter $Wc$ to the
counter $CW$; then start the in-range clauses for the symbols $x = g - 1, \dots, 0$ when $b$ is
true, and the overflow clause otherwise. A clause $c$ (in-range, overflow or pushed fill)
prepends the terminator $00$ to the output, adds the counter $Vc$ to the counter $P$, runs the
literal routines of $c$ from the last down to the first, drains $P$ prepending $01$ per unit, and
goes on to the next clause of its chain; after the last pushed-fill clause it returns to the
fill drain of the block setup, and after the last in-range clause and after the overflow clause
the drain stages empty $CB$ and then $CW$ and return to the head of the in-range loop when $b$ is
true, and of the overflow loop otherwise. -/
def bdP (i : Fin N) (k : Fin L.KK) : BD L.g L.d → TM2.Stmt (SΓ CK) (Lab L N) Bool
  | .bC1 b => xfer (.c .KB) [⟨.c .CB, ()⟩, ⟨.c .tmp, ()⟩] (.b i k (.bC1 b)) (.b i k (.bC2 b))
  | .bC2 b => xfer (.c .tmp) [⟨.c .KB, ()⟩] (.b i k (.bC2 b))
      (if b then .b i k (.sM .head) else .b i k (.w1 b))
  | .sM s => mulS .U .md .Gc .CB .tmp (fun s => .b i k (.sM s)) (.b i k (.w1 true)) s
  | .w1 b => xfer (.c .CB) [⟨.c .CW, ()⟩, ⟨.c .tmp, ()⟩] (.b i k (.w1 b)) (.b i k (.w2 b))
  | .w2 b => xfer (.c .tmp) [⟨.c .CB, ()⟩] (.b i k (.w2 b)) (.b i k (.w3 b))
  | .w3 b => xfer (.c .Wc) [⟨.c .CW, ()⟩, ⟨.c .tmp, ()⟩] (.b i k (.w3 b)) (.b i k (.w4 b))
  | .w4 b => xfer (.c .tmp) [⟨.c .Wc, ()⟩] (.b i k (.w4 b))
      (if b then GL.xFrom i k L.g else .b i k (.e00 .ov))
  | .e00 c => emitR .out [false, false] (.b i k (.cv1 c))
  | .cv1 c => xfer (.c .Vc) [⟨.c .P, ()⟩, ⟨.c .tmp, ()⟩] (.b i k (.cv1 c)) (.b i k (.cv2 c))
  | .cv2 c => xfer (.c .tmp) [⟨.c .Vc, ()⟩] (.b i k (.cv2 c)) (GL.after i k c c.nl)
  | .lit c l s => litP L sa pl cn pu N i k c l s
  | .fin c => xferE (.c .P) .out [false, true] (.b i k (.fin c)) (GL.nextC i k c)
  | .dCB b => xfer (.c .CB) [] (.b i k (.dCB b)) (.b i k (.dCW b))
  | .dCW b => xfer (.c .CW) [] (.b i k (.dCW b)) (if b then .s i k .sHead else .s i k .oHead)

/-- **The cell-shift generator.** For a layout $L$ with label block size $A$, $K$ stacks and $g$
symbol codes, tables $s_a, p, c, p_u$ and $N$ situations, the counter machine with the unit
counters of the generator and a Boolean output stack, meant to start with $T$ units on
$\mathrm{Tn}$, $H$ on $\mathrm{Hs}$ and everything else empty. Its precomputation puts $g$ units
on $\mathrm{Gc}$, adds $\mathrm{Hs} \cdot \mathrm{Gc}$ to $\mathrm{HG}$, puts $A$ units on
$\mathrm{Wc}$ and $K$ on $\mathrm{Ka}$, adds $\mathrm{Ka} \cdot \mathrm{HG}$ to $\mathrm{Wc}$,
drains $\mathrm{Ka}$, adds $\mathrm{Tn} \cdot \mathrm{Wc}$ to $\mathrm{Vc}$ and then adds
$\mathrm{Wc}$ to $\mathrm{Vc}$. The time loop then pops one unit of $\mathrm{Tn}$ per iteration,
pushing it on $\mathrm{Ti}$; each iteration adds $\mathrm{Tn} \cdot \mathrm{Wc}$ to
$\mathrm{TW}$, adds $\mathrm{TW}$ and then $\mathrm{Wc}$ to $\mathrm{TW1}$, runs the blocks of
all $N$ situations, and drains $\mathrm{TW}$ and $\mathrm{TW1}$. When $\mathrm{Tn}$ is empty it
moves $\mathrm{Ti}$ back onto $\mathrm{Tn}$ and halts at $\mathrm{done}$. The stages of a block
$(i, k)$ run the block routine, its loop-body stages run the loop-body routine, and its
decrement stages pop $\mathrm{U}$ and continue the decrement chain, halting at $\mathrm{bad}$ if
$\mathrm{U}$ is empty. Additions go through the scratch counters $\mathrm{md}$ and $\mathrm{tmp}$
and restore their sources when the scratch counters start empty. -/
def prog : Lab L N → TM2.Stmt (SΓ CK) (Lab L N) Bool
  | .pre .eg => emitR (.c .Gc) (List.replicate L.g ()) (.pre (.hg .head))
  | .pre (.hg s) => mulS .Hs .md .Gc .HG .tmp (fun s => .pre (.hg s)) (.pre .ew) s
  | .pre .ew => emitR (.c .Wc) (List.replicate L.A ()) (.pre .ek)
  | .pre .ek => emitR (.c .Ka) (List.replicate L.KK ()) (.pre (.w .head))
  | .pre (.w s) => mulS .Ka .md .HG .Wc .tmp (fun s => .pre (.w s)) (.pre .dk) s
  | .pre .dk => xfer (.c .Ka) [] (.pre .dk) (.pre (.v .head))
  | .pre (.v s) => mulS .Tn .md .Wc .Vc .tmp (fun s => .pre (.v s)) (.pre .vw1) s
  | .pre .vw1 => xfer (.c .Wc) [⟨.c .Vc, ()⟩, ⟨.c .tmp, ()⟩] (.pre .vw1) (.pre .vw2)
  | .pre .vw2 => xfer (.c .tmp) [⟨.c .Wc, ()⟩] (.pre .vw2) .tHead
  | .tHead => forHead (.c .Tn) (.c .Ti) () (.tw .head) .tRest
  | .tRest => xfer (.c .Ti) [⟨.c .Tn, ()⟩] .tRest .done
  | .tw s => mulS .Tn .md .Wc .TW .tmp .tw .t1a s
  | .t1a => xfer (.c .TW) [⟨.c .TW1, ()⟩, ⟨.c .tmp, ()⟩] .t1a .t1b
  | .t1b => xfer (.c .tmp) [⟨.c .TW, ()⟩] .t1b .t1c
  | .t1c => xfer (.c .Wc) [⟨.c .TW1, ()⟩, ⟨.c .tmp, ()⟩] .t1c .t1d
  | .t1d => xfer (.c .tmp) [⟨.c .Wc, ()⟩] .t1d (GL.iFrom N)
  | .tEnd => xfer (.c .TW) [] .tEnd .tEnd2
  | .tEnd2 => xfer (.c .TW1) [] .tEnd2 .tHead
  | .s i k x => stP L pl cn N i k x
  | .sb i k r => decr (.c .U) .bad (GL.sbL i k r.val)
  | .b i k x => bdP L sa pl cn pu N i k x
  | .bad => .halt
  | .done => .halt

/-- **The cell-shift generator as a finite stack machine.** For a layout $L$, situation tables
$\mathrm{sa}$, $\mathrm{pl}$, $\mathrm{cn}$, $\mathrm{pu}$ and $N$ situations, the cell-shift
generator for these data, bundled as a multi-stack Turing machine with finitely many stacks,
labels and states: its stacks are the Boolean output stack and one counter stack for each counter
of the generator, its input stack is the counter $\mathrm{Tn}$ and its output stack is the Boolean
output stack, its alphabets are the counter-machine alphabets (Booleans on the output stack, a
unit symbol on each counter), its labels are the labels of the shift generator for $L$ and $N$,
execution starts at the first precomputation stage, its internal state is a Boolean, initially
false, and its transition function is the cell-shift generator.

It serves only to check that the generator meets the finiteness conditions of a finite machine. -/
def shTM : FinTM2 where
  K := SK CK
  k₀ := .c .Tn
  k₁ := .out
  Γ := SΓ CK
  Λ := Lab L N
  main := .pre .eg
  σ := Bool
  initialState := false
  m := prog L sa pl cn pu N

end Machine

/-! ## [FAM] Clause kinds: literal positions -/

section Lits

variable {g d : ℕ}

theorem BS.k_ne (b : BS) : b.k ≠ .Q ∧ b.k ≠ .tmp ∧ b.k ≠ .P ∧ b.k ≠ .c1 ∧ b.k ≠ .c2 ∧ b.k ≠ .md :=
  by cases b <;> decide

/-- **Literals of a clause kind at given positions.** Let $c$ be a clause kind with $n$ literals
($n = 3$ for an in-range shift clause, $n = 2$ for an overflow-fill or pushed-fill clause) and let
$\mathrm{pos} : \mathbb{N} \to \mathbb{N}$. The literals of $c$ at positions $\mathrm{pos}$ are the
list $(\mathrm{pos}(0), b_0), \dots, (\mathrm{pos}(n - 1), b_{n - 1})$ of variable-sign pairs,
where the sign $b_l$ is true (a positive literal) exactly when $l = n - 1$. -/
def clits (pos : ℕ → ℕ) (cl : CL g d) : List (ℕ × Bool) :=
  (List.range cl.nl).map fun l => (pos l, cl.sg l)

/-- **Increasing literal positions below a bound.** For $p : \mathbb{N} \to \mathbb{N}$ and
$n, V \in \mathbb{N}$, the positions $p$ are increasing for $n$ literals below $V$ when
$p(l) < p(l + 1)$ for every $l$ with $l + 1 < n$, and $p(n - 1) < V$ if $n \ge 1$. -/
structure Mono (pos : ℕ → ℕ) (n V : ℕ) : Prop where
  mono : ∀ l, l + 1 < n → pos l < pos (l + 1)
  last : ∀ l, l + 1 = n → pos l < V

theorem clits_drop (pos : ℕ → ℕ) (cl : CL g d) (l : ℕ) :
    (clits pos cl).drop l = (List.range' l (cl.nl - l)).map fun l => (pos l, cl.sg l) := by
  rw [clits, ← List.map_drop, List.range_eq_range', List.drop_range']; simp

/-- **Boundary before a literal.** For $V, n, l \in \mathbb{N}$ and literal positions
$pos : \mathbb{N} \to \mathbb{N}$, the boundary before literal $l$ is $pos(l)$ if $l < n$, and $V$
otherwise. -/
def bnd (V : ℕ) (pos : ℕ → ℕ) (n l : ℕ) : ℕ := if l < n then pos l else V

theorem inc_drop {V : ℕ} {pos : ℕ → ℕ} {cl : CL g d} (h : Mono pos cl.nl V) (l : ℕ)
    (hl : l ≤ cl.nl) : Inc (bnd V pos cl.nl l) ((clits pos cl).drop l) V := by
  rw [clits_drop]
  refine inc_of_mono _ cl.nl V (fun j hj => h.mono j hj) (fun j hj => h.last j hj) (cl.nl - l) l _
    (by omega) (fun hn => ?_) (fun _ => ?_)
  · simp only [bnd]; split_ifs with h'
    · omega
    · exact le_rfl
  · simp only [bnd, ite_eq_left (show l < cl.nl by omega)]; exact le_rfl

theorem bnd_le {V : ℕ} {pos : ℕ → ℕ} {cl : CL g d} (h : Mono pos cl.nl V) {l : ℕ} (hl : l ≤ cl.nl) :
    bnd V pos cl.nl l ≤ V := (inc_drop h l hl).le

theorem bnd_lt {V : ℕ} {pos : ℕ → ℕ} {n l : ℕ} (h : Mono pos n V) (hl : l < n) :
    pos l < bnd V pos n (l + 1) := by
  unfold bnd
  split_ifs with h'
  · exact h.mono l h'
  · exact h.last l (by omega)

end Lits

/-! ## [FAM] Correctness: one literal, one clause -/

section Clause

variable {L : Layout} {sa : ℕ → ℕ} {pl cn : ℕ → ℕ → ℕ} {pu : ℕ → ℕ → ℕ → ℕ} {N : ℕ}

/-- **Empty scratch counters of the shift generator.** A valuation $F$ of the generator's counters
satisfies this predicate when the five scratch counters $Q$, $\mathit{tmp}$, $\mathit{md}$, $c_1$
and $c_2$ all have value $0$ under $F$. The generator keeps them empty whenever a clause starts. -/
structure Rest (F : CK → ℕ) : Prop where
  Q : F .Q = 0
  tmp : F .tmp = 0
  md : F .md = 0
  c1 : F .c1 = 0
  c2 : F .c2 = 0

theorem Rest.upd {F : CK → ℕ} (h : Rest F) {x : CK} (hQ : x ≠ .Q) (ht : x ≠ .tmp) (hm : x ≠ .md)
    (h1 : x ≠ .c1) (h2 : x ≠ .c2) (n : ℕ) : Rest (update F x n) :=
  ⟨by rw [update_of_ne hQ.symm, h.Q], by rw [update_of_ne ht.symm, h.tmp],
    by rw [update_of_ne hm.symm, h.md], by rw [update_of_ne h1.symm, h.c1],
    by rw [update_of_ne h2.symm, h.c2]⟩

/-- **One literal routine of the cell-shift generator.** Let $i < N$ be a situation, $k < K$ a
stack, $c$ a clause kind and $l < 3$ a literal index. Let $F$ be counter values whose scratch
counters ($Q$, the copy buffer, the multiplication buffer and the two comparison buffers) are
$0$, let $b$ be the value under $F$ of the base counter of literal $l$, and let $a$ be the
constant offset of literal $l$ of $c$ in block $(i, k)$. Let $q, m \in \mathbb{N}$ satisfy
$q = b + a$ and $F(P) = q + m + 1$. Then for every output $o$ and internal state $v$, the
generator goes in at most $m(3q + 6) + 2b + 4q + 9$ steps from the start of the routine of
literal $l$, with state $v$, counters $F$ and output $o$, to the start of the routine of literal
$l - 1$ (the end-of-clause label of $c$ when $l = 0$), with state false, counters $F$ except
that $P = q$, and output the slot code of literal $l$ (sign positive exactly when $l$ is the last
literal of $c$), followed by $m$ copies of $01$, followed by $o$. -/
theorem lit_run (i : Fin N) (k : Fin L.KK) (c : CL L.g L.d) (l : Fin 3) (F : CK → ℕ) (hF : Rest F)
    (q gap : ℕ) (hq : q = F (c.bs l).k + csv L sa pl cn pu N i k c l) (hp : F .P = q + gap + 1)
    (o : List Bool) (v : Bool) :
    RunLe (prog L sa pl cn pu N) (gap * (3 * q + 6) + 2 * F (c.bs l).k + 4 * q + 9)
      ⟨some (.b i k (.lit c l .cp1)), v, st F o⟩
      ⟨some (GL.after i k c l), false,
        st (update F .P q) (encodeSlot (some (c.sg l)) ++ rep [false, true] gap ++ o)⟩ := by
  obtain ⟨hQ, htmp, hmd, hc1, hc2⟩ := hF
  obtain ⟨n1, n2, n3, -, -, -⟩ := BS.k_ne (c.bs l)
  refine Bud.start ?_
  refine (copyS (M := prog L sa pl cn pu N) (l₁ := .b i k (.lit c l .cp1))
    (l₂ := .b i k (.lit c l .cp2)) (next := .b i k (.lit c l .eo)) rfl rfl n1 n2 (by decide) F
    htmp v o).bud ?_
  refine (emitS (M := prog L sa pl cn pu N) (self := .b i k (.lit c l .eo))
    (next := .b i k (.lit c l .dec)) rfl _ _ _).bud ?_
  refine (gapS (M := prog L sa pl cn pu N) (P := .P) (Q := .Q) (T1 := .c1) (T2 := .c2)
    (ys := [false, true]) (dec := .b i k (.lit c l .dec)) (cmpL := .b i k (.lit c l .cmp))
    (emitL := .b i k (.lit c l .emL)) (ifZero := .b i k (.lit c l .bad))
    (next := .b i k (.lit c l .slot)) (r := fun o => .b i k (.lit c l (.r o)))
    (rB := fun o => .b i k (.lit c l (.rB o)))
    (out := fun o => if o = .eq then .b i k (.lit c l .slot) else .b i k (.lit c l .emL))
    rfl rfl (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) rfl (by decide) q gap _
    (by simp [hp]) (by simp [hQ, hq]; omega) (by simp [hc1]) (by simp [hc2]) _ _).bud ?_
  refine (emitOut (M := prog L sa pl cn pu N) (self := .b i k (.lit c l .slot))
    (next := .b i k (.lit c l .dq)) rfl _ _ _).bud ?_
  refine (drainS (M := prog L sa pl cn pu N) (self := .b i k (.lit c l .dq)) (next := GL.after i k c l)
    (x := .Q) rfl _ _ _).bud ?_
  refine Bud.fin ?_ ?_
  · simp [hQ, hq]; omega
  · rw [List.append_assoc]
    congr 2
    funext x; cases x <;> simp [hQ, hq]

/-- **Per-literal step overhead of the cell-shift generator.** For $V \in \mathbb{N}$, the
per-literal overhead is $6V + 9$.

It is the step budget for emitting one literal of a clause over $V$ variables, not counting the
loop that emits the gap before the literal. -/
def litE (V : ℕ) : ℕ := 6 * V + 9

/-- **Step bound for one clause.** For a natural number $V$ (the number of variables), the step
bound for one clause of at most three literals is $V(3V + 6) + 3(6V + 9) + 3V + 4$, where
$6V + 9$ is the per-literal cost apart from the gap loop. -/
def clauseB (V : ℕ) : ℕ := V * (3 * V + 6) + 3 * litE V + 3 * V + 4

/-- **The literal routines of one clause of the cell-shift generator.** Fix $V \in \mathbb{N}$, a
situation $i < N$, a stack $k < K$, a clause kind $c$ with $n$ literals, positions
$p : \mathbb{N} \to \mathbb{N}$, counter values $F$ whose scratch counters are $0$, and an output
$o$. Suppose that for every $l$ the position $p(l)$ is the value under $F$ of the base counter of
literal $l$ plus its constant offset in block $(i, k)$, that this base value is at most $V$, that
$p(l) < p(l + 1)$ whenever $l + 1 < n$, and that $p(n - 1) < V$ if $n \ge 1$. Let
$\beta(l) = p(l)$ for $l < n$ and $\beta(l) = V$ otherwise, and let $E(l)$ be the gap encoding,
from slot $\beta(l)$ up to $V$, of literals $l, \dots, n - 1$ of $c$ at positions $p$, each
with sign positive exactly when it is the last literal. Then for every $l \le n$ and every
internal state $v$ there is a state $v'$ such that the generator goes in at most
$\beta(l)(3V + 6) + l(6V + 9)$ steps from the start of the routine of literal $l - 1$ (the
end-of-clause label of $c$ when $l = 0$), with state $v$, counters $F$ except that
$P = \beta(l)$, and output $E(l)$ followed by $00$ and $o$, to the end-of-clause label of $c$,
with state $v'$, counters $F$ except that $P = \beta(0)$, and output $E(0)$ followed by $00$
and $o$. -/
theorem lits_run {V : ℕ} (i : Fin N) (k : Fin L.KK) {c : CL L.g L.d} (pos : ℕ → ℕ) (F : CK → ℕ)
    (hF : Rest F) (hpos : ∀ l, pos l = F (c.bs l).k + csv L sa pl cn pu N i k c l)
    (hbase : ∀ l, F (c.bs l).k ≤ V) (hM : Mono pos c.nl V) (o : List Bool) :
    ∀ l, l ≤ c.nl → ∀ v : Bool, ∃ v' : Bool,
      RunLe (prog L sa pl cn pu N) (bnd V pos c.nl l * (3 * V + 6) + l * litE V)
        ⟨some (GL.after i k c l), v,
          st (update F .P (bnd V pos c.nl l)) (gapEnc (bnd V pos c.nl l) ((clits pos c).drop l) V ++
            [false, false] ++ o)⟩
        ⟨some (.b i k (.fin c)), v',
          st (update F .P (bnd V pos c.nl 0)) (gapEnc (bnd V pos c.nl 0) (clits pos c) V ++
            [false, false] ++ o)⟩ := by
  intro l
  induction l with
  | zero => intro _ v; exact ⟨v, by simpa [GL.after] using RunLe.refl _ _⟩
  | succ l ih =>
      intro hl v
      have hlm : l < c.nl := by omega
      have hl3 : l < 3 := lt_of_lt_of_le hlm c.nl_le
      set p := pos l with hp
      set b := bnd V pos c.nl (l + 1) with hb
      have hpb : p < b := bnd_lt hM hlm
      obtain ⟨-, -, nP, -, -, -⟩ := BS.k_ne (c.bs l)
      have r := lit_run (sa := sa) (pl := pl) (cn := cn) (pu := pu) i k c ⟨l, hl3⟩ (update F .P b)
        (hF.upd (by decide) (by decide) (by decide) (by decide) (by decide) b) p (b - p - 1)
        (by simp [hp, hpos, update_of_ne nP]) (by simp; omega)
        (gapEnc b ((clits pos c).drop (l + 1)) V ++ [false, false] ++ o) v
      obtain ⟨v', r'⟩ := ih (by omega) false
      refine ⟨v', ?_⟩
      rw [GL.after, ite_eq_right (Nat.succ_ne_zero l), Nat.add_sub_cancel, GL.litL_of_lt hl3]
      refine Bud.start (r.bud ?_)
      rw [update_idem]
      have hbl : bnd V pos c.nl l = p := by simp [bnd, hlm, hp]
      have hdrop : (clits pos c).drop l = (p, c.sg l) :: (clits pos c).drop (l + 1) := by
        rw [clits_drop, clits_drop, show c.nl - l = (c.nl - (l + 1)) + 1 by omega,
          List.range'_succ, List.map_cons]
      have hshift := gapEnc_shift (show p + 1 ≤ b by omega) (inc_drop hM (l + 1) hl)
      rw [hbl, hdrop, gapEnc, Nat.sub_self, rep_zero, List.nil_append, hshift,
        show b - (p + 1) = b - p - 1 by omega] at r'
      simp only [List.append_assoc] at r' ⊢
      refine r'.bud (Bud.fin ?_ rfl)
      have hbV := bnd_le hM hl
      have h1 := Nat.mul_le_mul_left (b - p - 1) (show 3 * p + 6 ≤ 3 * V + 6 by omega)
      have h2 : (b - p - 1) * (3 * V + 6) + p * (3 * V + 6) ≤ b * (3 * V + 6) := by
        rw [← Nat.add_mul]; exact Nat.mul_le_mul_right _ (by omega)
      have h3 := hbase l
      simp only [update_of_ne nP]
      rw [Nat.add_one_mul l]
      unfold litE
      omega

/-- **One clause of the cell-shift generator.** Let $M$ be the cell-shift generator for a layout
$L$ with $K$ stacks, $g$ symbol codes and window depth $d$, situation offsets $\mathrm{sa}$, push
counts $\mathrm{pl}$, consumed counts $\mathrm{cn}$, pushed codes $\mathrm{pu}$ and $N$
situations. Fix a situation $i < N$, a stack $k < K$, a clause kind $c$ with parameters $g$ and
$d$ and with $n$ literals, positions $\mathrm{pos} : \mathbb{N} \to \mathbb{N}$, counter values $F$
and $V \in \mathbb{N}$. For each $l \in \mathbb{N}$ let $b_l$ be the counter holding the base of
literal $l$ of $c$ and $o_l$ the constant offset of literal $l$ of $c$ in block $(i, k)$. Assume
that the scratch counters $\mathrm{Q}$, $\mathrm{tmp}$, $\mathrm{md}$, $\mathrm{c1}$ and
$\mathrm{c2}$ are zero in $F$; that $\mathrm{pos}(l) = F(b_l) + o_l$ and $F(b_l) \le V$ for every
$l \in \mathbb{N}$; that $\mathrm{pos}(l) < \mathrm{pos}(l + 1)$ whenever $l + 1 < n$ and
$\mathrm{pos}(n - 1) < V$; and that $F(\mathrm{Vc}) = V$ and $F(\mathrm{P}) = 0$. Then for every
output word $w$ and flag $v$, $M$ runs in at most $V(3V + 6) + 3(6V + 9) + 3V + 4$ steps (the step
bound for one clause) from the configuration with label $\mathrm{e00}(c)$ of block $(i, k)$, flag
$v$, counter values $F$ and output $w$ to the configuration with the label that follows clause $c$
in block $(i, k)$, flag false, counter values $F$ and output $e$ followed by $w$, where $e$ is the
encoding of the dense clause over $V$ variables whose literals are those of $c$ at positions
$\mathrm{pos}$. -/
theorem clause_run {V : ℕ} (i : Fin N) (k : Fin L.KK) {c : CL L.g L.d} (pos : ℕ → ℕ) (F : CK → ℕ)
    (hF : Rest F) (hpos : ∀ l, pos l = F (c.bs l).k + csv L sa pl cn pu N i k c l)
    (hbase : ∀ l, F (c.bs l).k ≤ V) (hM : Mono pos c.nl V) (hV : F .Vc = V) (hP : F .P = 0)
    (o : List Bool) (v : Bool) :
    RunLe (prog L sa pl cn pu N) (clauseB V) ⟨some (.b i k (.e00 c)), v, st F o⟩
      ⟨some (GL.nextC i k c), false, st F (encodeClause (denseClause V (clits pos c)) ++ o)⟩ := by
  refine Bud.start ?_
  refine (emitOut (M := prog L sa pl cn pu N) (self := .b i k (.e00 c)) (next := .b i k (.cv1 c)) rfl
    _ _ _).bud ?_
  refine (copyS (M := prog L sa pl cn pu N) (l₁ := .b i k (.cv1 c)) (l₂ := .b i k (.cv2 c))
    (next := GL.after i k c c.nl) rfl rfl (by decide) (by decide) (by decide) F hF.tmp v _).bud ?_
  obtain ⟨v', r⟩ := lits_run i k pos F hF hpos hbase hM o c.nl le_rfl false
  have hbm : bnd V pos c.nl c.nl = V := by simp [bnd]
  rw [hbm, List.drop_eq_nil_of_le (by simp [clits]), gapEnc, Nat.sub_self, rep_zero,
    List.nil_append] at r
  rw [hV, hP, Nat.add_zero]
  refine r.bud ?_
  refine (xferES (M := prog L sa pl cn pu N) (self := .b i k (.fin c)) (next := GL.nextC i k c)
    (x := .P) rfl _ _ _).bud ?_
  have e1 : update (update F .P (bnd V pos c.nl 0)) .P 0 = F := by
    rw [update_idem, ← hP, update_eq_self]
  have h0 := inc_drop hM 0 (Nat.zero_le _)
  rw [List.drop_zero] at h0
  have e2 : encodeClause (denseClause V (clits pos c)) =
      rep [false, true] (bnd V pos c.nl 0) ++ gapEnc (bnd V pos c.nl 0) (clits pos c) V ++
        [false, false] := by
    rw [encodeClause_denseClause (Family.Inc.mono_lo (Nat.zero_le _) h0),
      gapEnc_shift (Nat.zero_le _) h0, Nat.sub_zero]
  simp only [update_self]
  rw [e1, e2]
  simp only [List.append_assoc]
  refine Bud.fin ?_ rfl
  have := bnd_le hM (l := 0) (Nat.zero_le _)
  have := Nat.mul_le_mul_right (litE V) c.nl_le
  unfold clauseB
  omega

end Clause

/-! ## [FAM] The shift and overflow clauses; the `x` chain; the decrement chain -/

section Cells

variable {L : Layout} {sa : ℕ → ℕ} {pl cn : ℕ → ℕ → ℕ} {pu : ℕ → ℕ → ℕ → ℕ} {N : ℕ}

/-- **First cell variable of a block.** For a layout with label block size $A$, $K$ stacks
and $g$ symbol codes, a stack height $H$, a time $t$ and a stack $k$, this is the number
$k \cdot (H g) + (t W + A)$, where $W = A + K H g$ is the number of variables per time step.
It is the index of the variable for depth $0$ and symbol code $0$ of stack $k$ in row $t$. -/
def kbv (L : Layout) (H t k : ℕ) : ℕ := k * (H * L.g) + (t * L.rowW H + L.A)

/-- **Literal positions of an in-range shift clause.** For a layout $L$ with label block size $A$,
$K$ stacks and $g$ symbol codes, row width $W = A + K H g$, situation offsets $s_a$, push counts
$p$, consumed counts $c$ and numbers $H, t, i, k, u, x, l$, the position of literal $l$ of the
in-range shift clause $(t, i, k, u, x)$ is: if $l = 0$, the cell variable of row $t$, stack $k$,
depth $u + c(i, k)$ and symbol code $x$, namely $t W + A + (k H + u + c(i, k)) g + x$; if
$l = 1$, the situation variable $(t + 1) W + s_a(i)$; and if $l \ge 2$, the cell variable of row
$t + 1$, stack $k$, depth $u + p(i, k)$ and symbol code $x$, namely
$(t + 1) W + A + (k H + u + p(i, k)) g + x$. -/
def shPos (L : Layout) (sa : ℕ → ℕ) (pl cn : ℕ → ℕ → ℕ) (H t i k u x l : ℕ) : ℕ :=
  if l = 0 then L.cIdx H t k (u + cn i k) x else if l = 1 then L.xIdx H (t + 1) (sa i)
  else L.cIdx H (t + 1) k (u + pl i k) x

/-- **Literal positions of an overflow clause.** For a layout $L$ with label block size $A$, $K$
stacks and $g$ symbol codes, row width $W = A + K H g$, situation offsets $s_a$, push counts $p$,
consumed counts $c$ and numbers $H, t, i, k, r, l$, the position of literal $l$ of the overflow
clause $(t, i, k, r)$ is the situation variable $(t + 1) W + s_a(i)$ if $l = 0$, and otherwise the
cell variable of row $t + 1$, stack $k$, depth $H - c(i, k) + p(i, k) + r$ and symbol code $0$,
namely $(t + 1) W + A + (k H + H - c(i, k) + p(i, k) + r) g$. Subtraction is truncated at $0$. -/
def ovPos (L : Layout) (sa : ℕ → ℕ) (pl cn : ℕ → ℕ → ℕ) (H t i k r l : ℕ) : ℕ :=
  if l = 0 then L.xIdx H (t + 1) (sa i) else L.cIdx H (t + 1) k (H - cn i k + pl i k + r) 0

theorem rowW_le {T H t : ℕ} (ht : t < T) : (t + 1) * L.rowW H + L.rowW H ≤ L.numVars T H := by
  unfold Layout.numVars
  rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)

theorem cw_le {T H t k j : ℕ} (ht : t < T) (hk : k < L.KK) (hj : j < H) :
    j * L.g + kbv L H t k + L.rowW H ≤ L.numVars T H := by
  have := Cslib.Complexity.CookLevin.OneHot.base_le (L := L) (T := T) (H := H) (t := t + 1) (k := k) (j := j) ht hk hj
  unfold kbv; rw [Nat.succ_mul] at this; omega

theorem kbw_le {T H t k : ℕ} (ht : t < T) (hk : k < L.KK) :
    kbv L H t k + L.rowW H ≤ L.numVars T H := by
  have h1 := rowW_le (L := L) (H := H) ht
  have h2 := Nat.mul_le_mul_right (H * L.g) hk.le
  have h3 : (t + 1) * L.rowW H = t * L.rowW H + L.rowW H := Nat.succ_mul _ _
  have h4 : L.rowW H = L.A + L.KK * (H * L.g) := rfl
  unfold kbv; omega

theorem shPos_mono {T H t : ℕ} {i : Fin N} {k : Fin L.KK} {u x : ℕ} (ht : t < T)
    (hwf : WF L sa pl cn pu N H) (hu : u + max (pl i k) (cn i k) < H) (hx : x < L.g) :
    Mono (shPos L sa pl cn H t i k u x) 3 (L.numVars T H) := by
  have hs := hwf.sa_lt i i.2
  have h1 := cIdx_lt_next_row (L := L) (t := t) k.2 (show u + cn i k < H by omega) hx
  have h2 := cIdx_lt_next_row (L := L) (t := t + 1) k.2 (show u + pl i k < H by omega) hx
  have h3 := rowW_le (L := L) (H := H) ht
  have h4 : (t + 1 + 1) * L.rowW H = (t + 1) * L.rowW H + L.rowW H := Nat.succ_mul _ _
  have e0 : shPos L sa pl cn H t i k u x 0 = L.cIdx H t k (u + cn i k) x := rfl
  have e1 : shPos L sa pl cn H t i k u x 1 = (t + 1) * L.rowW H + sa i := rfl
  have e2 : shPos L sa pl cn H t i k u x 2 = L.cIdx H (t + 1) k (u + pl i k) x := rfl
  have e2' : L.cIdx H (t + 1) k (u + pl i k) x =
      (t + 1) * L.rowW H + L.A + (k * H + (u + pl i k)) * L.g + x := rfl
  refine ⟨fun l hl => ?_, fun l hl => ?_⟩
  · obtain rfl | rfl : l = 0 ∨ l = 1 := by omega
    · rw [e0, show 0 + 1 = 1 from rfl, e1]; omega
    · rw [e1, show 1 + 1 = 2 from rfl, e2]; omega
  · obtain rfl : l = 2 := by omega
    rw [e2]; omega

theorem ovPos_mono {T H t : ℕ} {i : Fin N} {k : Fin L.KK} {r : ℕ} (ht : t < T)
    (hwf : WF L sa pl cn pu N H) (hr : r < cn i k - pl i k) :
    Mono (ovPos L sa pl cn H t i k r) 2 (L.numVars T H) := by
  have hs := hwf.sa_lt i i.2
  have hc := hwf.cn_le i i.2 k k.2
  have hd := hwf.d_le
  have h2 := cIdx_lt_next_row (L := L) (t := t + 1) k.2
    (show H - cn i k + pl i k + r < H by omega) hwf.g_pos
  have h3 := rowW_le (L := L) (H := H) ht
  have h4 : (t + 1 + 1) * L.rowW H = (t + 1) * L.rowW H + L.rowW H := Nat.succ_mul _ _
  have h5 : (t + 1) * L.rowW H = t * L.rowW H + L.rowW H := Nat.succ_mul _ _
  have e0 : ovPos L sa pl cn H t i k r 0 = (t + 1) * L.rowW H + sa i := rfl
  have e1 : ovPos L sa pl cn H t i k r 1 = L.cIdx H (t + 1) k (H - cn i k + pl i k + r) 0 := rfl
  have e1' : L.cIdx H (t + 1) k (H - cn i k + pl i k + r) 0 =
      (t + 1) * L.rowW H + L.A + (k * H + (H - cn i k + pl i k + r)) * L.g + 0 := rfl
  refine ⟨fun l hl => ?_, fun l hl => ?_⟩
  · obtain rfl : l = 0 := by omega
    rw [e0, show 0 + 1 = 1 from rfl, e1]; omega
  · obtain rfl : l = 1 := by omega
    rw [e1]; omega

theorem clits_sh (H t : ℕ) (i : Fin N) (k : Fin L.KK) (u x : ℕ) (hx : x < L.g) :
    clits (shPos L sa pl cn H t i k u x) (.sh ⟨x,
        hx⟩ : CL L.g L.d) = shLits L sa pl cn H t i k u x := by
  simp [clits, CL.nl, CL.sg, shPos, shLits, List.range_succ]

theorem clits_ov (H t : ℕ) (i : Fin N) (k : Fin L.KK) (r : ℕ) :
    clits (ovPos L sa pl cn H t i k r) (.ov : CL L.g L.d) = ovLits L sa pl cn H t i k r := by
  simp [clits, CL.nl, CL.sg, ovPos, ovLits, List.range_succ]

/-- **Literal positions of a pushed-fill clause.** For a layout $L$ with label block size $A$,
$K$ stacks and $g$ symbol codes, row width $W = A + K H g$, situation offsets $s_a$, pushed codes
$p_u$ and numbers $H, t, i, k, j, l$, the position of literal $l$ of the pushed-fill clause
$(t, i, k, j)$ is the situation variable $(t + 1) W + s_a(i)$ if $l = 0$, and otherwise the cell
variable of row $t + 1$, stack $k$, depth $j$ and symbol code $p_u(i, k, j)$, namely
$(t + 1) W + A + (k H + j) g + p_u(i, k, j)$. -/
def pfPos (L : Layout) (sa : ℕ → ℕ) (pu : ℕ → ℕ → ℕ → ℕ) (H t i k j l : ℕ) : ℕ :=
  if l = 0 then L.xIdx H (t + 1) (sa i) else L.cIdx H (t + 1) k j (pu i k j)

theorem pfPos_mono {T H t : ℕ} {i : Fin N} {k : Fin L.KK} {j : ℕ} (ht : t < T)
    (hwf : WF L sa pl cn pu N H) (hj : j < pl i k) :
    Mono (pfPos L sa pu H t i k j) 2 (L.numVars T H) := by
  have hs := hwf.sa_lt i i.2
  have hp := hwf.pl_le i i.2 k k.2
  have hd := hwf.d_le
  have hx := hwf.pu_lt i i.2 k k.2 j hj
  have h2 := cIdx_lt_next_row (L := L) (t := t + 1) k.2 (show j < H by omega) hx
  have h3 := rowW_le (L := L) (H := H) ht
  have h4 : (t + 1 + 1) * L.rowW H = (t + 1) * L.rowW H + L.rowW H := Nat.succ_mul _ _
  have e0 : pfPos L sa pu H t i k j 0 = (t + 1) * L.rowW H + sa i := rfl
  have e1 : pfPos L sa pu H t i k j 1 = L.cIdx H (t + 1) k j (pu i k j) := rfl
  have e1' : L.cIdx H (t + 1) k j (pu i k j) =
      (t + 1) * L.rowW H + L.A + (k * H + j) * L.g + pu i k j := rfl
  refine ⟨fun l hl => ?_, fun l hl => ?_⟩
  · obtain rfl : l = 0 := by omega
    rw [e0, show 0 + 1 = 1 from rfl, e1]; omega
  · obtain rfl : l = 1 := by omega
    rw [e1]; omega

theorem clits_pf (H t : ℕ) (i : Fin N) (k : Fin L.KK) (j : ℕ) (hj : j < L.d) :
    clits (pfPos L sa pu H t i k j) (.pf ⟨j, hj⟩ : CL L.g L.d) = pfLits L sa pu H t i k j := by
  simp [clits, CL.nl, CL.sg, pfPos, pfLits, List.range_succ]

/-- **Counter state of a loop body.** For a layout $L$ with label block size $A$, $KK$ stacks and
$g$ symbol codes, $T, H, t \in \mathbb{N}$ and counter contents $F$, let $W = A + KK \cdot H g$ be
the row width. The condition holds when the scratch counters $Q$, $tmp$, $md$, $c_1$, $c_2$ and
the counter $P$ are empty, $Vc$ holds the variable count $(T + 1) W$, $Gc$ holds $g$, $Wc$ holds
$W$, $TW$ holds $t W$ and $TW1$ holds $(t + 1) W$. -/
structure Body (L : Layout) (T H t : ℕ) (F : CK → ℕ) : Prop extends Rest F where
  P : F .P = 0
  Vc : F .Vc = L.numVars T H
  Gc : F .Gc = L.g
  Wc : F .Wc = L.rowW H
  TW : F .TW = t * L.rowW H
  TW1 : F .TW1 = (t + 1) * L.rowW H

/-- **The in-range chain of the cell-shift generator.** Let $L$ be a layout with label block size
$A$, $K$ stacks, $g$ symbol codes and window depth $d$, let $H, T \in \mathbb{N}$, let
$W = A + K H g$ be the row width and $V = (T + 1) W$ the number of variables, and let the tables
$\mathrm{sa}, \mathrm{pl}, \mathrm{cn}, \mathrm{pu}$ be well formed for $N$ situations and height
$H$: $g > 0$, $d \le H$, and for all $i < N$ and $k < K$, $\mathrm{sa}(i) < A$,
$\mathrm{pl}(i, k) \le d$, $\mathrm{cn}(i, k) \le d$ and $\mathrm{pu}(i, k, j) < g$ for every
$j < \mathrm{pl}(i, k)$. Let $t < T$, $i < N$, $k < K$ and $u \in \mathbb{N}$ with
$u + \max(\mathrm{pl}(i, k), \mathrm{cn}(i, k)) < H$, let $b = k H g + t W + A$ be the first
cell variable of stack $k$ in row $t$, and let $F$ be counter values in which $\mathrm{Q}$,
$\mathrm{tmp}$, $\mathrm{md}$, $\mathrm{c1}$, $\mathrm{c2}$ and $\mathrm{P}$ are $0$,
$F(\mathrm{Vc}) = V$, $F(\mathrm{Gc}) = g$, $F(\mathrm{Wc}) = W$, $F(\mathrm{TW}) = t W$,
$F(\mathrm{TW1}) = (t + 1) W$, $F(\mathrm{CB}) = u g + b$ and $F(\mathrm{CW}) = u g + b + W$.
Then for every $n \le g$, every output word $o$ and every flag $v$ there is a flag $v'$ such that
the generator for these data, started at the entry label of the in-range chain for $n$ in block
$(i, k)$ with flag $v$, counters $F$ and output $o$, reaches the in-range drain stage
$\mathrm{dCB}$ of block $(i, k)$ with flag $v'$, counters $F$ and output $e_0 e_1 \cdots e_{n-1}$
followed by $o$ in at most $n \cdot \mathrm{clauseB}(V)$ steps, where
$\mathrm{clauseB}(V) = V(3V + 6) + 3(6V + 9) + 3V + 4$ and $e_x$ is the encoding of the dense
clause over $V$ variables whose literals are the in-range shift literals for $(t, i, k, u, x)$. -/
theorem xs_run {T H t : ℕ} {i : Fin N} {k : Fin L.KK} {u : ℕ} (ht : t < T)
    (hwf : WF L sa pl cn pu N H) (hu : u + max (pl i k) (cn i k) < H) (F : CK → ℕ)
    (hF : Body L T H t F) (hCB : F .CB = u * L.g + kbv L H t k)
    (hCW : F .CW = u * L.g + kbv L H t k + L.rowW H) :
    ∀ n, n ≤ L.g → ∀ (o : List Bool) (v : Bool), ∃ v' : Bool,
      RunLe (prog L sa pl cn pu N) (n * clauseB (L.numVars T H)) ⟨some (GL.xFrom i k n), v, st F o⟩
        ⟨some (.b i k (.dCB true)), v', st F ((List.range n).flatMap (fun x =>
          encodeClause (denseClause (L.numVars T H) (shLits L sa pl cn H t i k u x))) ++ o)⟩ := by
  intro n
  induction n with
  | zero => intro _ o v; exact ⟨v, by simpa [GL.xFrom] using RunLe.refl _ _⟩
  | succ n ih =>
      intro hn o v
      have hng : n < L.g := by omega
      have hV := cw_le (L := L) (T := T) ht k.2 (show u < H by omega)
      have r := clause_run (sa := sa) (pl := pl) (cn := cn) (pu := pu) (V := L.numVars T H) i k
        (c := .sh ⟨n, hng⟩) (shPos L sa pl cn H t i k u n) F hF.toRest
        (fun l => by
          simp only [shPos, CL.bs, csv, CL.cs]
          split_ifs <;> simp only [BS.k, hF.TW1, hCB, hCW, kbv, Layout.xIdx, Layout.cIdx] <;> ring)
        (fun l => by
          have := rowW_le (L := L) (H := H) ht
          simp only [CL.bs]; split_ifs <;> simp only [BS.k, hF.TW1, hCB, hCW] <;> omega)
        (shPos_mono ht hwf hu hng) hF.Vc hF.P o v
      rw [show GL.nextC i k (CL.sh ⟨n, hng⟩) = GL.xFrom i k n from rfl, clits_sh] at r
      rw [GL.xFrom_succ hng]
      obtain ⟨v', r'⟩ := ih (by omega) _ false
      refine ⟨v', Bud.start (r.bud (r'.bud (Bud.fin ?_ ?_)))⟩
      · rw [Nat.succ_mul]; omega
      · rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]

/-- **The pushed-fill chain of the cell-shift generator.** Let $L$ be a layout with label block
size $A$, $K$ stacks and $g$ symbol codes, let $W = A + K H g$ be the row width and
$V = (T + 1) W$ the number of variables, and let the tables $s_a, p, c, p_u$ be well formed for
$N$ situations and height $H$. Let $t < T$, $i < N$, $k < K$, and let $F$ be counter values in
which $\mathrm{Q}$, $\mathrm{tmp}$, $\mathrm{md}$, $\mathrm{c1}$, $\mathrm{c2}$ and $\mathrm{P}$
are $0$, $F(\mathrm{Vc}) = V$, $F(\mathrm{Gc}) = g$, $F(\mathrm{Wc}) = W$, $F(\mathrm{TW}) = t W$,
$F(\mathrm{TW1}) = (t + 1) W$ and $F(\mathrm{CW}) = k H g + t W + A + W$. Then for every
$n \le p(i, k)$, every output word $o$ and every flag $v$ there is a flag $v'$ such that the
generator for these data, started at the entry label of the pushed-fill chain for $n$ in block
$(i, k)$ with flag $v$, counters $F$ and output $o$, reaches the fill-drain stage $\mathrm{fD1}$
of block $(i, k)$ (before draining) with flag $v'$, counters $F$ and output
$e_0 e_1 \cdots e_{n-1}$ followed by $o$ in at most $n \cdot \mathrm{clauseB}(V)$ steps, where
$\mathrm{clauseB}(V) = 3 V^2 + 27 V + 31$ and $e_j$ is the encoding of the dense clause over $V$
variables whose literals are those of the pushed-fill clause $(t, i, k, j)$. -/
theorem pf_run {T H t : ℕ} {i : Fin N} {k : Fin L.KK} (ht : t < T)
    (hwf : WF L sa pl cn pu N H) (F : CK → ℕ) (hF : Body L T H t F)
    (hCW : F .CW = kbv L H t k + L.rowW H) :
    ∀ n, n ≤ pl i k → ∀ (o : List Bool) (v : Bool), ∃ v' : Bool,
      RunLe (prog L sa pl cn pu N) (n * clauseB (L.numVars T H))
        ⟨some (GL.pfFrom i k n), v, st F o⟩
        ⟨some (.s i k .fD1), v', st F ((List.range n).flatMap (fun j =>
          encodeClause (denseClause (L.numVars T H) (pfLits L sa pu H t i k j))) ++ o)⟩ := by
  intro n
  induction n with
  | zero => intro _ o v; exact ⟨v, by simpa [GL.pfFrom] using RunLe.refl _ _⟩
  | succ n ih =>
      intro hn o v
      have hnd : n < L.d := by have := hwf.pl_le i i.2 k k.2; omega
      have r := clause_run (sa := sa) (pl := pl) (cn := cn) (pu := pu) (V := L.numVars T H) i k
        (c := .pf ⟨n, hnd⟩) (pfPos L sa pu H t i k n) F hF.toRest
        (fun l => by
          simp only [pfPos, CL.bs, csv, CL.cs]
          split_ifs
          · simp only [BS.k, hF.TW1, Layout.xIdx]
          · simp only [BS.k, hCW, kbv, Layout.cIdx]; ring)
        (fun l => by
          have := rowW_le (L := L) (H := H) ht
          have := kbw_le (L := L) (H := H) ht k.2
          simp only [CL.bs]; split_ifs <;> simp only [BS.k, hF.TW1, hCW] <;> omega)
        (pfPos_mono ht hwf (by omega)) hF.Vc hF.P o v
      rw [show GL.nextC i k (CL.pf ⟨n, hnd⟩ : CL L.g L.d) = GL.pfFrom i k n from rfl,
        clits_pf] at r
      rw [GL.pfFrom_succ hnd]
      obtain ⟨v', r'⟩ := ih (by omega) _ false
      refine ⟨v', Bud.start (r.bud (r'.bud (Bud.fin ?_ ?_)))⟩
      · rw [Nat.succ_mul]; omega
      · rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]

/-- **The decrement chain takes $n$ steps.** Fix a layout with $K$ stacks and window depth $d$,
the generator's remaining parameters with $N$ situations, a situation $i < N$ and a stack $k < K$.
For every $n \le d + 1$, every counter valuation $F$ and every $h$ with $F(U) = h + n$, every flag
$v$ and every output $o$, there is a flag $v'$ such that the generator, started at the
decrement-chain label for $n$ remaining decrements of block $(i, k)$ with flag $v$, counters $F$
and output $o$, reaches in exactly $n$ steps the pushed-fill setup label of block $(i, k)$ with
flag $v'$, the counters $F$ with $U$ set to $h$, and the same output $o$. -/
theorem sb_run (i : Fin N) (k : Fin L.KK) :
    ∀ n, n ≤ L.d + 1 → ∀ (F : CK → ℕ) (h : ℕ), F .U = h + n → ∀ (v : Bool) (o : List Bool),
      ∃ v' : Bool, Run (prog L sa pl cn pu N) n ⟨some (GL.sbL i k n), v, st F o⟩
        ⟨some (.s i k .fC1), v', st (update F .U h) o⟩ := by
  intro n
  induction n with
  | zero =>
      intro _ F h hF v o
      refine ⟨v, ?_⟩
      rw [show update F .U h = F by rw [update_eq_self_iff]; omega]
      exact Run.zero _
  | succ n ih =>
      intro hn F h hF v o
      have r := decS (M := prog L sa pl cn pu N) (self := .sb i k ⟨n, by omega⟩)
        (ifZero := .bad) (ifPos := GL.sbL i k n) (x := .U) rfl F (h + n) (by omega) v o
      obtain ⟨v', r'⟩ := ih (by omega) (update F .U (h + n)) h (by simp) true o
      rw [update_idem] at r'
      refine ⟨v', ?_⟩
      rw [GL.sbL_succ (by omega), show n + 1 = 1 + n by omega]
      exact r.trans r'

end Cells

/-! ## [FAM] Correctness: the two runtime loop bodies -/

section Bodies

variable {L : Layout} {sa : ℕ → ℕ} {pl cn : ℕ → ℕ → ℕ} {pu : ℕ → ℕ → ℕ → ℕ} {N : ℕ}

theorem Body.upd {T H t : ℕ} {F : CK → ℕ} (h : Body L T H t F) {x : CK}
    (hx : x ≠ .Q ∧ x ≠ .tmp ∧ x ≠ .md ∧ x ≠ .c1 ∧ x ≠ .c2 ∧ x ≠ .P ∧ x ≠ .Vc ∧ x ≠ .Gc ∧
      x ≠ .Wc ∧ x ≠ .TW ∧ x ≠ .TW1) (n : ℕ) : Body L T H t (update F x n) := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := hx
  exact ⟨h.toRest.upd a1 a2 a3 a4 a5 n, by rw [update_of_ne a6.symm, h.P],
    by rw [update_of_ne a7.symm, h.Vc], by rw [update_of_ne a8.symm, h.Gc],
    by rw [update_of_ne a9.symm, h.Wc], by rw [update_of_ne a10.symm, h.TW],
    by rw [update_of_ne a11.symm, h.TW1]⟩

theorem kbv_le {T H t k : ℕ} (ht : t < T) (hk : k < L.KK) : kbv L H t k ≤ L.numVars T H :=
  Cslib.Complexity.CookLevin.OneHot.kb_le (by omega) hk

theorem rowW_le' {T H : ℕ} : L.rowW H ≤ L.numVars T H := by
  unfold Layout.numVars; exact Nat.le_mul_of_pos_left _ (Nat.succ_pos _)

/-- **Step bound for one in-range loop iteration.** For natural numbers $g$, $H$ and $V$, with
$B(V)$ the cost bound of one clause over $V$ variables, the bound is
$(2V + 2) + (H(2g + 3) + H + 2) + (2V + 2) + (2V + 2) + g \cdot B(V) + (V + 1) + (V + 1)$. -/
def sBodyB (g H V : ℕ) : ℕ :=
  (2 * V + 2) + (H * (2 * g + 3) + H + 2) + (2 * V + 2) + (2 * V + 2) + g * clauseB V + (V + 1) +
    (V + 1)

/-- **Step budget of one overflow iteration of the cell-shift generator.** For
$g, H, d, V \in \mathbb{N}$, the budget is

$$(2H + 2) + (2d + 2) + (H(2g + 3) + H + 2) + (H + 1) + 3(2V + 2) + B(V) + 2(V + 1),$$

where $B(V) = V(3V + 6) + 3(6V + 9) + 3V + 4$ is the step budget of one clause. It bounds the
steps of one iteration of the overflow loop. -/
def oBodyB (g H d V : ℕ) : ℕ :=
  (2 * H + 2) + (2 * d + 2) + (H * (2 * g + 3) + H + 2) + (H + 1) + (2 * V + 2) + (2 * V + 2) +
    (2 * V + 2) + clauseB V + (V + 1) + (V + 1)

/-- **One iteration of the in-range loop of the cell-shift generator.** Let $L$ be a layout with
label block size $A$, $K$ stacks, $g$ symbol codes and window depth $d$, let $T, H \in \mathbb{N}$,
let $W = A + K H g$ be the row width and $V = (T + 1) W$ the number of variables, and let the
situation-offset, push-count, consumed-count and pushed-code tables $s_a, p, c, p_u$ be well
formed for $N$ situations and height $H$. Let $t < T$, $i < N$, $k < K$ and $u \in \mathbb{N}$
with $u + \max(p(i, k), c(i, k)) < H$. Let $F$ be counter values in which $\mathrm{Q}$,
$\mathrm{tmp}$, $\mathrm{md}$, $\mathrm{c1}$, $\mathrm{c2}$, $\mathrm{P}$, $\mathrm{CB}$ and
$\mathrm{CW}$ are $0$, $F(\mathrm{Vc}) = V$, $F(\mathrm{Gc}) = g$, $F(\mathrm{Wc}) = W$,
$F(\mathrm{TW}) = t W$, $F(\mathrm{TW1}) = (t + 1) W$, $F(\mathrm{KB}) = k H g + t W + A$ and
$F(\mathrm{U}) = u$. Then for every output word $o$ and flag $v$, the generator for these data,
started at the in-range variant of the first loop-body stage $\mathrm{bC1}$ of block $(i, k)$
with flag $v$, counters $F$ and output $o$, reaches the in-range loop head $\mathrm{sHead}$ of
block $(i, k)$ with flag false, counters $F$ and output $e_0 e_1 \cdots e_{g-1}$ followed by $o$
in at most $3(2V + 2) + (H(2g + 3) + H + 2) + g B(V) + 2(V + 1)$ steps, where
$B(V) = V(3V + 6) + 3(6V + 9) + 3V + 4$ is the step budget of one clause and $e_x$ is the
encoding of the dense clause over $V$ variables whose literals are the in-range shift literals
for $(t, i, k, u, x)$. -/
theorem sbody_run {T H t : ℕ} {i : Fin N} {k : Fin L.KK} {u : ℕ} (ht : t < T)
    (hwf : WF L sa pl cn pu N H) (hu : u + max (pl i k) (cn i k) < H) (F : CK → ℕ)
    (hF : Body L T H t F) (hKB : F .KB = kbv L H t k) (hU : F .U = u) (hCB : F .CB = 0)
    (hCW : F .CW = 0) (o : List Bool) (v : Bool) :
    RunLe (prog L sa pl cn pu N) (sBodyB L.g H (L.numVars T H)) ⟨some (.b i k (.bC1 true)), v,
        st F o⟩
      ⟨some (.s i k .sHead), false, st F ((List.range L.g).flatMap (fun x =>
          encodeClause (denseClause (L.numVars T H) (shLits L sa pl cn H t i k u x))) ++ o)⟩ := by
  have hV := cw_le (L := L) (T := T) ht k.2 (show u < H by omega)
  have hW := rowW_le' (L := L) (T := T) (H := H)
  set cb := u * L.g + kbv L H t k with hcb
  refine Bud.start ?_
  refine (copyS (M := prog L sa pl cn pu N) (l₁ := .b i k (.bC1 true)) (l₂ := .b i k (.bC2 true))
    (next := .b i k (.sM .head)) rfl rfl (by decide) (by decide) (by decide) F hF.tmp v o).bud ?_
  refine (mulS_run (M := prog L sa pl cn pu N) (mk := fun s => .b i k (.sM s))
    (next := .b i k (.w1 true)) (a := .U) (ad := .md) (b := .Gc) (c := .CB) (t := .tmp)
    (fun _ => rfl) (by decide) _ (by simp [hF.md]) (by simp [hF.tmp]) _ _).bud ?_
  refine (copyS (M := prog L sa pl cn pu N) (l₁ := .b i k (.w1 true)) (l₂ := .b i k (.w2 true))
    (next := .b i k (.w3 true)) rfl rfl (by decide) (by decide) (by decide) _ (by simp [hF.tmp]) _
    _).bud ?_
  refine (copyS (M := prog L sa pl cn pu N) (l₁ := .b i k (.w3 true)) (l₂ := .b i k (.w4 true))
    (next := GL.xFrom i k L.g) rfl rfl (by decide) (by decide) (by decide) _ (by simp [hF.tmp]) _
    _).bud ?_
  refine bud_st (F' := update (update F .CB cb) .CW (cb + L.rowW H)) (by
    funext x; cases x <;> simp [hKB, hU, hF.Gc, hF.Wc, hCB, hCW, hcb]; omega) ?_
  have hF' : Body L T H t (update (update F .CB cb) .CW (cb + L.rowW H)) :=
    (hF.upd (by decide) cb).upd (by decide) _
  obtain ⟨v1,
      rx⟩ := xs_run (sa := sa) (pu := pu) ht hwf hu _ hF' (by simp [hcb]) (by simp [hcb]) L.g le_rfl o
    false
  refine rx.bud ?_
  refine (drainS (M := prog L sa pl cn pu N) (self := .b i k (.dCB true))
    (next := .b i k (.dCW true)) (x := .CB) rfl _ _ _).bud ?_
  refine (drainS (M := prog L sa pl cn pu N) (self := .b i k (.dCW true)) (next := .s i k .sHead)
    (x := .CW) rfl _ _ _).bud ?_
  refine Bud.fin ?_ ?_
  · have h1 := Nat.mul_le_mul_right (2 * L.g + 3) (show u ≤ H by omega)
    have h2 := kbv_le (L := L) (H := H) ht k.2
    simp only [update_self, ne_eq, reduceCtorEq, not_false_eq_true, update_of_ne, hKB, hU, hF.Gc,
      hF.Wc, hCB, hCW, Nat.add_zero]
    unfold sBodyB
    omega
  · congr 2
    funext x; cases x <;> simp [hCB, hCW]

/-- **One iteration of the overflow loop of the cell-shift generator.** Let $L$ be a layout with
label block size $A$, $K$ stacks, $g$ symbol codes and window depth $d$, let $W = A + K H g$ be the
row width and $V = (T + 1) W$ the number of variables, and let the tables $s_a, p, c, p_u$ be well
formed for $N$ situations and height $H$. Let $t < T$, $i < N$, $k < K$ and
$r < c(i, k) - p(i, k)$. Let $F$ be counter values in which $\mathrm{Q}$, $\mathrm{tmp}$,
$\mathrm{md}$, $\mathrm{c1}$, $\mathrm{c2}$, $\mathrm{P}$, $\mathrm{Ka}$, $\mathrm{CB}$ and
$\mathrm{CW}$ are $0$, $F(\mathrm{Vc}) = V$, $F(\mathrm{Gc}) = g$, $F(\mathrm{Wc}) = W$,
$F(\mathrm{TW}) = t W$, $F(\mathrm{TW1}) = (t + 1) W$, $F(\mathrm{KB}) = k H g + t W + A$,
$F(\mathrm{U}) = H - \max(p(i, k), c(i, k))$ and $F(\mathrm{R}) = r$. Then for every output word
$o$ and flag $v$, the generator for these data, started at stage $\mathrm{oC1}$ of block $(i, k)$
with flag $v$, counters $F$ and output $o$, reaches stage $\mathrm{oHead}$ of block $(i, k)$ with
flag false, counters $F$ and output $e$ followed by $o$ in at most
$\mathrm{oBodyB}(g, H, d, V) = 3 V^2 + 35 V + 2 g H + 7 H + 2 d + 46$ steps, where $e$ is the
encoding of the dense clause over $V$ variables whose literals are those of the overflow clause
$(t, i, k, r)$. -/
theorem obody_run {T H t : ℕ} {i : Fin N} {k : Fin L.KK} {r : ℕ} (ht : t < T)
    (hwf : WF L sa pl cn pu N H) (hr : r < cn i k - pl i k) (F : CK → ℕ)
    (hF : Body L T H t F) (hKB : F .KB = kbv L H t k) (hU : F .U = H - max (pl i k) (cn i k))
    (hR : F .R = r) (hKa : F .Ka = 0) (hCB : F .CB = 0) (hCW : F .CW = 0) (o : List Bool)
    (v : Bool) :
    RunLe (prog L sa pl cn pu N) (oBodyB L.g H L.d (L.numVars T H)) ⟨some (.s i k .oC1), v, st F o⟩
      ⟨some (.s i k .oHead), false,
        st F (encodeClause (denseClause (L.numVars T H) (ovLits L sa pl cn H t i k r)) ++ o)⟩ := by
  have hc := hwf.cn_le i i.2 k k.2
  have hd := hwf.d_le
  have hm : max (pl i k) (cn i k) = cn i k := max_eq_right (by omega)
  have hV := cw_le (L := L) (T := T) ht k.2 (show H - cn i k + r < H by omega)
  have hW := rowW_le' (L := L) (T := T) (H := H)
  set cb := (H - cn i k + r) * L.g + kbv L H t k with hcb
  rw [hm] at hU
  refine Bud.start ?_
  refine (copyS (M := prog L sa pl cn pu N) (l₁ := .s i k .oC1) (l₂ := .s i k .oC2)
    (next := .s i k .oR1) rfl rfl (by decide) (by decide) (by decide) F hF.tmp v o).bud ?_
  refine (copyS (M := prog L sa pl cn pu N) (l₁ := .s i k .oR1) (l₂ := .s i k .oR2)
    (next := .s i k (.oM .head)) rfl rfl (by decide) (by decide) (by decide) _ (by simp [hF.tmp]) _
    _).bud ?_
  refine (mulS_run (M := prog L sa pl cn pu N) (mk := fun s => .s i k (.oM s))
    (next := .s i k .oD) (a := .Ka) (ad := .md) (b := .Gc) (c := .CB) (t := .tmp)
    (fun _ => rfl) (by decide) _ (by simp [hF.md]) (by simp [hF.tmp]) _ _).bud ?_
  refine (drainS (M := prog L sa pl cn pu N) (self := .s i k .oD) (next := .b i k (.bC1 false))
    (x := .Ka) rfl _ _ _).bud ?_
  refine (copyS (M := prog L sa pl cn pu N) (l₁ := .b i k (.bC1 false)) (l₂ := .b i k (.bC2 false))
    (next := .b i k (.w1 false)) rfl rfl (by decide) (by decide) (by decide) _ (by simp [hF.tmp]) _
    _).bud ?_
  refine (copyS (M := prog L sa pl cn pu N) (l₁ := .b i k (.w1 false)) (l₂ := .b i k (.w2 false))
    (next := .b i k (.w3 false)) rfl rfl (by decide) (by decide) (by decide) _ (by simp [hF.tmp]) _
    _).bud ?_
  refine (copyS (M := prog L sa pl cn pu N) (l₁ := .b i k (.w3 false)) (l₂ := .b i k (.w4 false))
    (next := .b i k (.e00 .ov)) rfl rfl (by decide) (by decide) (by decide) _ (by simp [hF.tmp]) _
    _).bud ?_
  refine bud_st (F' := update (update F .CB cb) .CW (cb + L.rowW H)) (by
    funext x; cases x <;> simp [hKB, hU, hR, hKa, hF.Gc, hF.Wc, hCB, hCW, hcb] <;> ring) ?_
  have hF' : Body L T H t (update (update F .CB cb) .CW (cb + L.rowW H)) :=
    (hF.upd (by decide) cb).upd (by decide) _
  have rc := clause_run (sa := sa) (pl := pl) (cn := cn) (pu := pu) (V := L.numVars T H) i k (c := .ov)
    (ovPos L sa pl cn H t i k r) _ hF'.toRest
    (fun l => by
      simp only [ovPos, CL.bs, csv, CL.cs]
      split_ifs
      · simp [BS.k, hF.TW1, Layout.xIdx]
      · simp only [BS.k, update_self, hcb, kbv, Layout.cIdx]
        have : H - cn i k + pl i k + r = H - cn i k + r + pl i k := by omega
        rw [this]; ring)
    (fun l => by
      have := rowW_le (L := L) (H := H) ht
      simp only [CL.bs]; split_ifs <;> simp [BS.k, hF.TW1] <;> omega)
    (ovPos_mono ht hwf hr) (by simp [hF.Vc]) (by simp [hF.P]) o false
  rw [clits_ov] at rc
  refine rc.bud ?_
  refine (drainS (M := prog L sa pl cn pu N) (self := .b i k (.dCB false))
    (next := .b i k (.dCW false)) (x := .CB) rfl _ _ _).bud ?_
  refine (drainS (M := prog L sa pl cn pu N) (self := .b i k (.dCW false)) (next := .s i k .oHead)
    (x := .CW) rfl _ _ _).bud ?_
  refine Bud.fin ?_ ?_
  · have h1 := Nat.mul_le_mul_right (2 * L.g + 3) (show r + (H - cn i k) ≤ H by omega)
    have h2 := kbv_le (L := L) (H := H) ht k.2
    have h3 : (r + (H - cn i k)) * L.g = (H - cn i k + r) * L.g := by ring
    simp only [update_self, ne_eq, reduceCtorEq, not_false_eq_true, update_of_ne, hKB, hU, hR,
      hKa, hF.Gc, hF.Wc, hCB, hCW, Nat.add_zero]
    unfold oBodyB
    omega
  · congr 2
    funext x; cases x <;> simp [hCB, hCW]

end Bodies

/-! ## [FAM] Correctness: one `(i, k)` block, the label chains, the time loop, the generator -/

section Top

variable {L : Layout} {sa : ℕ → ℕ} {pl cn : ℕ → ℕ → ℕ} {pu : ℕ → ℕ → ℕ → ℕ} {N : ℕ}

/-- **Counter state at the start of a block.** For a layout $L$ with $g$ symbol codes,
$T, H, t \in \mathbb{N}$ and counter contents $F$: $F$ is a loop-body counter state for
$L, T, H, t$, the counters $KB$, $U$, $Ui$, $R$, $Ri$, $Ka$, $CB$ and $CW$ are empty, $HG$ holds
$H \cdot g$ and $Hs$ holds $H$. -/
structure Blk (L : Layout) (T H t : ℕ) (F : CK → ℕ) : Prop extends Body L T H t F where
  KB : F .KB = 0
  U : F .U = 0
  Ui : F .Ui = 0
  R : F .R = 0
  Ri : F .Ri = 0
  Ka : F .Ka = 0
  CB : F .CB = 0
  CW : F .CW = 0
  HG : F .HG = H * L.g
  Hs : F .Hs = H

/-- **Step budget for one block of the shift generator.** For natural numbers $g$, $K$, $H$,
$d$ and $V$ (in use: the number of symbol codes, the number of stacks, the stack height, the
window depth and the number of variables), the budget is
$$
1 + (2V + 2) + 1 + \bigl(K(2V + 3) + K + 2\bigr) + (K + 1) + (2H + 2) + d + 1 +
\bigl((2V + 2) + (2V + 2) + d\,c(V) + (V + 1)\bigr) + \bigl(d\,(o + 1) + d + 2\bigr) +
\bigl(H\,(s + 1) + H + 2\bigr) + (H + 1) + (d + 1) + (V + 1),
$$
where $c(V)$ is the step budget of one clause, $o$ is the step budget $o(g, H, d, V)$ of one
iteration of the overflow loop, and $s$ is the step budget $s(g, H, V)$ of one iteration of
the in-range loop. -/
def ikB (g KK H d V : ℕ) : ℕ :=
  1 + (2 * V + 2) + 1 + (KK * (2 * V + 3) + KK + 2) + (KK + 1) + (2 * H + 2) + d + 1 +
    ((2 * V + 2) + (2 * V + 2) + d * clauseB V + (V + 1)) +
    (d * (oBodyB g H d V + 1) + d + 2) + (H * (sBodyB g H V + 1) + H + 2) + (H + 1) + (d + 1) +
    (V + 1)

theorem encodeCNF_shBlk (T H t i k : ℕ) :
    encodeCNF (shBlk L sa pl cn pu T H t i k) =
      (List.range (H - max (pl i k) (cn i k))).flatMap (fun u => (List.range L.g).flatMap
        fun x => encodeClause (denseClause (L.numVars T H) (shLits L sa pl cn H t i k u x))) ++
      (List.range (cn i k - pl i k)).flatMap
        (fun r => encodeClause (denseClause (L.numVars T H) (ovLits L sa pl cn H t i k r))) ++
      (List.range (pl i k)).flatMap
        (fun j => encodeClause (denseClause (L.numVars T H) (pfLits L sa pu H t i k j))) := by
  simp [encodeCNF, shBlk, List.flatMap_append, List.flatMap_assoc, List.flatMap_map]

theorem hg_le {T H : ℕ} (hK : 0 < L.KK) : H * L.g ≤ L.numVars T H := by
  have h1 : H * L.g ≤ L.KK * (H * L.g) := Nat.le_mul_of_pos_left _ hK
  have h2 := rowW_le' (L := L) (T := T) (H := H)
  unfold Layout.rowW at h2; omega

/-- **Correctness of the shift generator on one block.** Let $t < T$, assume the
well-formedness conditions for $N$ situations and stack height $H$, let $i < N$ and $k < K$,
where $K$ is the number of stacks, and let $F$ be counter values satisfying the block-start
conditions at time $t$. Then for every output $o$ and every Boolean state $v$, the generator,
started at the first setup stage of block $(i, k)$ with state $v$, counters $F$ and output $o$,
reaches in at most $B$ steps the entry label of the stacks $< k$ of situation $i$, with state
false, counters $F$ and output $e$ followed by $o$. Here $e$ is the encoding of the clause block
of situation $i$, stack $k$ at time $t$, and $B$ is the step budget for one block with
$V = (T + 1) W$ variables, $W$ being the number of variables per time step. -/
theorem ik_run {T H t : ℕ} (ht : t < T) (hwf : WF L sa pl cn pu N H) (i : Fin N) (k : Fin L.KK)
    (F : CK → ℕ) (hF : Blk L T H t F) (o : List Bool) (v : Bool) :
    RunLe (prog L sa pl cn pu N) (ikB L.g L.KK H L.d (L.numVars T H)) ⟨some (.s i k .kbE), v,
        st F o⟩
      ⟨some (GL.ik i.val k.val), false, st F (encodeCNF (shBlk L sa pl cn pu T H t i k) ++ o)⟩ := by
  have hp := hwf.pl_le i i.2 k k.2
  have hc := hwf.cn_le i i.2 k k.2
  have hd := hwf.d_le
  have hmd : max (pl i k) (cn i k) ≤ L.d := max_le hp hc
  have hmp : pl i k ≤ max (pl i k) (cn i k) := le_max_left _ _
  have hmc : cn i k ≤ max (pl i k) (cn i k) := le_max_right _ _
  set m := max (pl i k) (cn i k) with hm
  refine Bud.start ?_
  refine (emitS (M := prog L sa pl cn pu N) (self := .s i k .kbE) (next := .s i k .kbC1) (x := .KB)
    rfl _ _ _).bud ?_
  refine (copyS (M := prog L sa pl cn pu N) (l₁ := .s i k .kbC1) (l₂ := .s i k .kbC2)
    (next := .s i k .kbK) rfl rfl (by decide) (by decide) (by decide) _ (by simp [hF.tmp]) v
    o).bud ?_
  refine (emitS (M := prog L sa pl cn pu N) (self := .s i k .kbK) (next := .s i k (.kbM .head))
    (x := .Ka) rfl _ _ _).bud ?_
  refine (mulS_run (M := prog L sa pl cn pu N) (mk := fun s => .s i k (.kbM s))
    (next := .s i k .kbD) (a := .Ka) (ad := .md) (b := .HG) (c := .KB) (t := .tmp)
    (fun _ => rfl) (by decide) _ (by simp [hF.md]) (by simp [hF.tmp]) _ _).bud ?_
  refine (drainS (M := prog L sa pl cn pu N) (self := .s i k .kbD) (next := .s i k .uC1) (x := .Ka)
    rfl _ _ _).bud ?_
  refine (copyS (M := prog L sa pl cn pu N) (l₁ := .s i k .uC1) (l₂ := .s i k .uC2)
    (next := GL.sbL i k m) rfl rfl (by decide) (by decide) (by decide) _ (by simp [hF.tmp]) _
    _).bud ?_
  refine bud_st (F' := update (update F .KB (kbv L H t k)) .U (H - m + m)) (by
    funext x; cases x <;> simp [hF.KB, hF.U, hF.Ka, hF.TW, hF.HG, hF.Hs, kbv]; omega) ?_
  obtain ⟨v1, rsb⟩ := sb_run (sa := sa) (pl := pl) (cn := cn) (pu := pu) i k m (by omega)
    (update (update F .KB (kbv L H t k)) .U (H - m + m)) (H - m) (by simp) false o
  refine rsb.bud ?_
  -- pushed fill
  set F1 := update (update F .KB (kbv L H t k)) .U (H - m) with hF1
  refine bud_st (F' := F1) (by funext x; cases x <;> simp [hF1]) ?_
  have hB1 : Body L T H t F1 := (hF.toBody.upd (by decide) _).upd (by decide) _
  refine (copyS (M := prog L sa pl cn pu N) (l₁ := .s i k .fC1) (l₂ := .s i k .fC2)
    (next := .s i k .fW1) rfl rfl (by decide) (by decide) (by decide) F1 hB1.tmp v1 o).bud ?_
  refine (copyS (M := prog L sa pl cn pu N) (l₁ := .s i k .fW1) (l₂ := .s i k .fW2)
    (next := GL.pfFrom i k (pl i k)) rfl rfl (by decide) (by decide) (by decide) _
    (by simp [hB1.tmp]) _ _).bud ?_
  set Ff := update F1 .CW (kbv L H t k + L.rowW H) with hFf
  refine bud_st (F' := Ff) (by
    funext x; cases x <;> simp [hFf, hF1, hF.CW, hF.Wc]; omega) ?_
  have hBf : Body L T H t Ff := hB1.upd (by decide) _
  obtain ⟨v2, rpf⟩ := pf_run (sa := sa) (cn := cn) (i := i) (k := k) ht hwf Ff hBf
    (by simp [hFf]) (pl i k) le_rfl o false
  refine rpf.bud ?_
  refine (drainS (M := prog L sa pl cn pu N) (self := .s i k .fD1) (next := .s i k .oE)
    (x := .CW) rfl _ _ _).bud ?_
  refine (emitS (M := prog L sa pl cn pu N) (self := .s i k .oE) (next := .s i k .oHead) (x := .R)
    rfl _ _ _).bud ?_
  set F2 := update (update (update F .KB (kbv L H t k)) .U (H - m)) .R (cn i k - pl i k) with hF2
  refine bud_st (F' := F2) (by
    funext x; cases x <;> simp [hF2, hFf, hF1, hF.R, hF.CW]) ?_
  have hB2 : Body L T H t F2 :=
    ((hF.toBody.upd (by decide) _).upd (by decide) _).upd (by decide) _
  have l1 := stLoop (M := prog L sa pl cn pu N) (c := .R) (cd := .Ri) (head := .s i k .oHead)
    (body := .s i k .oC1) (rest := .s i k .oRest) (next := .s i k .sHead) rfl rfl (by decide)
    (cn i k - pl i k) (oBodyB L.g H L.d (L.numVars T H))
    (fun r => encodeClause (denseClause (L.numVars T H) (ovLits L sa pl cn H t i k r))) F2
    (by simp [hF2]) (by simp [hF2, hF.Ri])
    (fun r hr o' => ⟨false, obody_run ht hwf hr _ ((hB2.upd (by decide) _).upd (by decide) _)
      (by simp [hF2]) (by simp [hF2, hm]) (by simp) (by simp [hF2, hF.Ka]) (by simp [hF2, hF.CB])
      (by simp [hF2, hF.CW]) o' true⟩)
    false ((List.range (pl i k)).flatMap (fun j =>
      encodeClause (denseClause (L.numVars T H) (pfLits L sa pu H t i k j))) ++ o)
  refine l1.bud ?_
  have l2 := stLoop (M := prog L sa pl cn pu N) (c := .U) (cd := .Ui) (head := .s i k .sHead)
    (body := .b i k (.bC1 true)) (rest := .s i k .sRest) (next := .s i k .dU) rfl rfl (by decide)
    (H - m) (sBodyB L.g H (L.numVars T H))
    (fun u => (List.range L.g).flatMap fun x =>
      encodeClause (denseClause (L.numVars T H) (shLits L sa pl cn H t i k u x))) F2
    (by simp [hF2]) (by simp [hF2, hF.Ui])
    (fun u hu o' => ⟨false, sbody_run ht hwf (by omega) _
      ((hB2.upd (by decide) _).upd (by decide) _) (by simp [hF2]) (by simp)
      (by simp [hF2, hF.CB]) (by simp [hF2, hF.CW]) o' true⟩)
    false ((List.range (cn i k - pl i k)).flatMap
      (fun r => encodeClause (denseClause (L.numVars T H) (ovLits L sa pl cn H t i k r))) ++
      ((List.range (pl i k)).flatMap (fun j =>
        encodeClause (denseClause (L.numVars T H) (pfLits L sa pu H t i k j))) ++ o))
  refine l2.bud ?_
  refine (drainS (M := prog L sa pl cn pu N) (self := .s i k .dU) (next := .s i k .dR) (x := .U) rfl _
    _ _).bud ?_
  refine (drainS (M := prog L sa pl cn pu N) (self := .s i k .dR) (next := .s i k .dKB) (x := .R) rfl
    _ _ _).bud ?_
  refine (drainS (M := prog L sa pl cn pu N) (self := .s i k .dKB) (next := GL.ik i.val k.val)
    (x := .KB) rfl _ _ _).bud ?_
  refine Bud.fin ?_ ?_
  · have h1 := kbv_le (L := L) (H := H) ht k.2
    have h2 : t * L.rowW H ≤ L.numVars T H := by
      unfold Layout.numVars; exact Nat.mul_le_mul_right _ (by omega)
    have hHG := hg_le (L := L) (T := T) (H := H) (Nat.lt_of_le_of_lt (Nat.zero_le _) k.2)
    have h3 : k.val * (2 * (H * L.g) + 3) ≤ L.KK * (2 * L.numVars T H + 3) :=
      Nat.mul_le_mul k.2.le (by omega)
    have h4 := Nat.mul_le_mul_right (oBodyB L.g H L.d (L.numVars T H) + 1)
      (show cn i k - pl i k ≤ L.d by omega)
    have h5 := Nat.mul_le_mul_right (sBodyB L.g H (L.numVars T H) + 1) (show H - m ≤ H by omega)
    have h6 := Nat.mul_le_mul_right (clauseB (L.numVars T H)) hp
    have h7 := kbw_le (L := L) (H := H) ht k.2
    have h8 := rowW_le' (L := L) (T := T) (H := H)
    simp only [update_self, ne_eq, reduceCtorEq, not_false_eq_true, update_of_ne, hF2, hFf, hF1,
      hF.KB, hF.Ka, hF.TW, hF.HG, hF.Hs, hF.Wc, hF.CW, Nat.add_zero]
    unfold ikB
    omega
  · simp only [encodeCNF_shBlk, List.append_assoc]
    congr 2
    funext x; cases x <;> simp [hF2, hF.KB, hF.U, hF.R]

/-- **Encoded blocks of one situation.** For a layout $L$ with $KK$ stacks, family data
$sa, pl, cn, pu$ and $T, H, t, i \in \mathbb{N}$, the bit string obtained by concatenating, for
$k = 0, \dots, KK - 1$ in order, the encoding of the clause block of situation $i$, stack $k$ at
time $t$. -/
def blkI (L : Layout) (sa : ℕ → ℕ) (pl cn : ℕ → ℕ → ℕ) (pu : ℕ → ℕ → ℕ → ℕ) (T H t i : ℕ) : List Bool :=
  (List.range L.KK).flatMap fun k => encodeCNF (shBlk L sa pl cn pu T H t i k)

/-- **Encoded blocks of one time step.** For a layout $L$, family data $sa, pl, cn, pu$ and
$N, T, H, t \in \mathbb{N}$, the bit string obtained by concatenating, for situations
$i = 0, \dots, N - 1$ in order, the encoded blocks of situation $i$ at time $t$. -/
def blkT (L : Layout) (sa : ℕ → ℕ) (pl cn : ℕ → ℕ → ℕ) (pu : ℕ → ℕ → ℕ → ℕ) (N T H t : ℕ) : List Bool :=
  (List.range N).flatMap (blkI L sa pl cn pu T H t)

/-- **Correctness of the shift generator on the stack chain of a situation.** Let $t < T$,
assume the well-formedness conditions for $N$ situations and stack height $H$, let $i < N$,
and let $F$ be counter values satisfying the block-start conditions at time $t$. Then for
every $n \le K$, where $K$ is the number of stacks, every output $o$ and every Boolean state
$v$, there is a Boolean state $v'$ such that the generator, started at the entry label of the
stacks $< n$ of situation $i$ with state $v$, counters $F$ and output $o$, reaches in at most
$n \cdot B$ steps the entry label of the situation chain for $i$, with state $v'$, counters $F$
and output $e_0 e_1 \cdots e_{n-1}$ followed by $o$. Here $e_k$ is the encoding of the clause
block of situation $i$, stack $k$ at time $t$, and $B$ is the step budget for one block with
$V = (T + 1) W$ variables, $W$ being the number of variables per time step. -/
theorem ks_run {T H t : ℕ} (ht : t < T) (hwf : WF L sa pl cn pu N H) (i : Fin N) (F : CK → ℕ)
    (hF : Blk L T H t F) :
    ∀ n, n ≤ L.KK → ∀ (o : List Bool) (v : Bool), ∃ v' : Bool,
      RunLe (prog L sa pl cn pu N) (n * ikB L.g L.KK H L.d (L.numVars T H))
        ⟨some (GL.ik i.val n), v, st F o⟩
        ⟨some (GL.iFrom i.val), v', st F ((List.range n).flatMap
          (fun k => encodeCNF (shBlk L sa pl cn pu T H t i k)) ++ o)⟩ := by
  intro n
  induction n with
  | zero => intro _ o v; exact ⟨v, by simpa [GL.ik] using RunLe.refl _ _⟩
  | succ n ih =>
      intro hn o v
      have r := ik_run ht hwf i ⟨n, by omega⟩ F hF o v
      obtain ⟨v', r'⟩ := ih (by omega) (encodeCNF (shBlk L sa pl cn pu T H t i n) ++ o) false
      refine ⟨v', ?_⟩
      rw [GL.ik_succ i.2 (by omega)]
      refine Bud.start (r.bud (r'.bud (Bud.fin ?_ ?_)))
      · rw [Nat.succ_mul]; omega
      · rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]

/-- **Correctness of the shift generator on the situation chain.** Let $t < T$, assume the
well-formedness conditions for $N$ situations and stack height $H$, and let $F$ be counter
values satisfying the block-start conditions at time $t$. Then for every $n \le N$, every
output $o$ and every Boolean state $v$, there is a Boolean state $v'$ such that the generator,
started at the entry label of the situation chain for $n$ with state $v$, counters $F$ and
output $o$, reaches in at most $n \cdot (K \cdot B)$ steps the end-of-time-step label with
state $v'$, counters $F$ and output $e_0 e_1 \cdots e_{n-1}$ followed by $o$. Here $K$ is the
number of stacks, $e_i$ is the concatenated encoding of the clause blocks of situation $i$ for
the stacks $0, \dots, K - 1$ at time $t$, and $B$ is the step budget for one block with
$V = (T + 1) W$ variables, $W$ being the number of variables per time step. -/
theorem is_run {T H t : ℕ} (ht : t < T) (hwf : WF L sa pl cn pu N H) (F : CK → ℕ)
    (hF : Blk L T H t F) :
    ∀ n, n ≤ N → ∀ (o : List Bool) (v : Bool), ∃ v' : Bool,
      RunLe (prog L sa pl cn pu N) (n * (L.KK * ikB L.g L.KK H L.d (L.numVars T H)))
        ⟨some (GL.iFrom n), v, st F o⟩
        ⟨some .tEnd, v', st F ((List.range n).flatMap (blkI L sa pl cn pu T H t) ++ o)⟩ := by
  by_cases hK : L.KK = 0
  · intro n _ o v
    refine ⟨v, ?_⟩
    rw [GL.iFrom_KK0 hK]
    have : (List.range n).flatMap (blkI L sa pl cn pu T H t) = [] := by simp [blkI, hK]
    rw [this, List.nil_append]
    exact RunLe.refl _ _
  intro n
  induction n with
  | zero => intro _ o v; exact ⟨v, by simpa [GL.iFrom] using RunLe.refl _ _⟩
  | succ n ih =>
      intro hn o v
      obtain ⟨v1, r⟩ := ks_run ht hwf ⟨n, by omega⟩ F hF L.KK le_rfl o v
      obtain ⟨v', r'⟩ := ih (by omega) (blkI L sa pl cn pu T H t n ++ o) v1
      refine ⟨v', ?_⟩
      rw [GL.iFrom_succ (by omega) (by omega)]
      refine Bud.start (r.bud (r'.bud (Bud.fin ?_ ?_)))
      · rw [Nat.succ_mul]; omega
      · rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]

/-- **Step budget for one time step of the shift generator.** Let $L$ be a layout with $K$
stacks, $g$ symbol codes and window depth $d$, let $N, T, H \in \mathbb{N}$, let $V = (T + 1) W$
be the number of variables, $W$ being the number of variables per time step at height $H$, and
let $B$ be the step budget for one block of the shift generator for $g$, $K$, $H$, $d$ and $V$.
The budget is

$$
\bigl(T(2V + 3) + T + 2\bigr) + (2V + 2) + (2V + 2) + N(K B) + (V + 1) + (V + 1).
$$
-/
def tBodyB (L : Layout) (N T H : ℕ) : ℕ :=
  (T * (2 * L.numVars T H + 3) + T + 2) + (2 * L.numVars T H + 2) + (2 * L.numVars T H + 2) +
    N * (L.KK * ikB L.g L.KK H L.d (L.numVars T H)) + (L.numVars T H + 1) + (L.numVars T H + 1)

/-- **One iteration of the time loop of the shift generator.** Let $L$ be a layout with $g$ symbol
codes, let $\mathrm{sa}$, $\mathrm{pl}$, $\mathrm{cn}$, $\mathrm{pu}$ be situation tables, let
$N, T, H, t \in \mathbb{N}$ with $t < T$, and suppose the tables are well formed for $N$
situations at height $H$. Write $W$ for the number of variables per time step at height $H$ and
$V = (T + 1) W$ for the number of variables. Let $F$ be counter values of the cell-shift generator
with empty scratch counters, with $\mathrm{Vc} = V$, $\mathrm{Gc} = g$, $\mathrm{Wc} = W$,
$\mathrm{Tn} = t$, $\mathrm{HG} = H g$ and $\mathrm{Hs} = H$, and with $\mathrm{P}$,
$\mathrm{TW}$, $\mathrm{TW1}$, $\mathrm{KB}$, $\mathrm{U}$, $\mathrm{Ui}$, $\mathrm{R}$,
$\mathrm{Ri}$, $\mathrm{Ka}$, $\mathrm{CB}$ and $\mathrm{CW}$ all $0$. Then for every output list
$o$ and every Boolean state $v$ there is a Boolean state $v'$ such that the generator, started at
the label $\mathrm{tw}(\mathrm{head})$ (the first stage of the time-loop multiplication) in state
$v$ with counters $F$ and output $o$, reaches the time-loop head $\mathrm{tHead}$ within at most
the step budget for one time step of the shift generator for $L$, $N$, $T$, $H$, in state $v'$
with counters $F$ and output the encoded blocks of time step $t$ followed by $o$. -/
theorem tbody_run {T H t : ℕ} (ht : t < T) (hwf : WF L sa pl cn pu N H) (F : CK → ℕ)
    (hF : Rest F) (hP : F .P = 0) (hV : F .Vc = L.numVars T H) (hG : F .Gc = L.g)
    (hW : F .Wc = L.rowW H) (hTW : F .TW = 0) (hTW1 : F .TW1 = 0) (hTn : F .Tn = t)
    (hKB : F .KB = 0) (hU : F .U = 0)
    (hUi : F .Ui = 0) (hR : F .R = 0) (hRi : F .Ri = 0) (hKa : F .Ka = 0) (hCB : F .CB = 0)
    (hCW : F .CW = 0) (hHG : F .HG = H * L.g) (hHs : F .Hs = H) (o : List Bool) (v : Bool) :
    ∃ v' : Bool, RunLe (prog L sa pl cn pu N) (tBodyB L N T H) ⟨some (.tw .head), v, st F o⟩
      ⟨some .tHead, v', st F (blkT L sa pl cn pu N T H t ++ o)⟩ := by
  set F1 := update (update F .TW (t * L.rowW H)) .TW1 ((t + 1) * L.rowW H) with hF1
  have hB : Blk L T H t F1 :=
    ⟨⟨(hF.upd (by decide) (by decide) (by decide) (by decide) (by decide) _).upd (by decide)
      (by decide) (by decide) (by decide) (by decide) _, by simp [hF1, hP], by simp [hF1, hV],
      by simp [hF1, hG], by simp [hF1, hW], by simp [hF1], by simp [hF1]⟩, by simp [hF1, hKB],
      by simp [hF1, hU], by simp [hF1, hUi], by simp [hF1, hR], by simp [hF1, hRi],
      by simp [hF1, hKa], by simp [hF1, hCB], by simp [hF1, hCW], by simp [hF1, hHG],
      by simp [hF1, hHs]⟩
  obtain ⟨v1, ri⟩ := is_run ht hwf _ hB N le_rfl o false
  refine ⟨false, Bud.start ?_⟩
  refine (mulS_run (M := prog L sa pl cn pu N) (mk := .tw) (next := .t1a) (a := .Tn) (ad := .md)
    (b := .Wc) (c := .TW) (t := .tmp) (fun _ => rfl) (by decide) _ (by simp [hF.md])
    (by simp [hF.tmp]) _ _).bud ?_
  refine (copyS (M := prog L sa pl cn pu N) (l₁ := .t1a) (l₂ := .t1b) (next := .t1c) rfl rfl
    (by decide) (by decide) (by decide) _ (by simp [hF.tmp]) _ _).bud ?_
  refine (copyS (M := prog L sa pl cn pu N) (l₁ := .t1c) (l₂ := .t1d) (next := GL.iFrom N) rfl rfl
    (by decide) (by decide) (by decide) _ (by simp [hF.tmp]) _ _).bud ?_
  refine bud_st (F' := F1) (by
    funext x; cases x <;> simp [hF1, hTn, hW, hTW, hTW1]; ring) ?_
  refine ri.bud ?_
  refine (drainS (M := prog L sa pl cn pu N) (self := .tEnd) (next := .tEnd2) (x := .TW) rfl _ _
    _).bud ?_
  refine (drainS (M := prog L sa pl cn pu N) (self := .tEnd2) (next := .tHead) (x := .TW1) rfl _ _
    _).bud ?_
  refine Bud.fin ?_ ?_
  · have h1 := Nat.mul_le_mul_right (2 * L.rowW H + 3) ht.le
    have h2 : t * L.rowW H ≤ L.numVars T H := by
      unfold Layout.numVars; exact Nat.mul_le_mul_right _ (by omega)
    have h3 := Nat.mul_le_mul_left T (show 2 * L.rowW H + 3 ≤ 2 * L.numVars T H + 3 by
      have := rowW_le' (L := L) (T := T) (H := H); omega)
    have h4 := rowW_le (L := L) (H := H) ht
    have h5 := rowW_le' (L := L) (T := T) (H := H)
    simp only [update_self, ne_eq, reduceCtorEq, not_false_eq_true, update_of_ne, hF1, hTn, hW,
      hTW, hTW1, Nat.add_zero, Nat.zero_add]
    unfold tBodyB
    omega
  · congr 2
    funext x; cases x <;> simp [hF1, hTW, hTW1]

/-- **Initial counter values of the shift generator.** For natural numbers $T$ and $H$, the
assignment of counter values that puts $T$ on the time-bound input counter, $H$ on the
stack-height input counter, and $0$ on every other counter of the generator. -/
def initF (T H : ℕ) : CK → ℕ
  | .Tn => T
  | .Hs => H
  | _ => 0

/-- **Counters after the precomputation of the cell-shift generator.** For a layout $L$ with label
block size $A$, $K$ stacks and $g$ symbol codes and numbers $T, H$, the counter values with $T$ on
$\mathrm{Tn}$, $H$ on $\mathrm{Hs}$, $g$ on $\mathrm{Gc}$, $H g$ on $\mathrm{HG}$, the row width
$W = A + K H g$ on $\mathrm{Wc}$, the number of variables $(T + 1) W$ on $\mathrm{Vc}$, and $0$
on every other counter. -/
def preF (L : Layout) (T H : ℕ) : CK → ℕ
  | .Tn => T
  | .Hs => H
  | .Gc => L.g
  | .HG => H * L.g
  | .Wc => L.rowW H
  | .Vc => L.numVars T H
  | _ => 0

/-- **Cost of the precomputation of the cell-shift generator.** For a layout $L$ with label block
size $A$, $K$ stacks and $g$ symbol codes, numbers $T$ and $H$, and the row width
$W = A + K H g$, this is the step bound

$$
1 + (H (2 g + 3) + H + 2) + 1 + 1 + (K (2 H g + 3) + K + 2) + (K + 1) +
(T (2 W + 3) + T + 2) + (2 W + 2).
$$
-/
def preB (L : Layout) (T H : ℕ) : ℕ :=
  1 + (H * (2 * L.g + 3) + H + 2) + 1 + 1 + (L.KK * (2 * (H * L.g) + 3) + L.KK + 2) + (L.KK + 1) +
    (T * (2 * L.rowW H + 3) + T + 2) + (2 * L.rowW H + 2)

/-- **Explicit time bound of the shift generator.** For a layout $L$ and $N, T, H \in \mathbb{N}$,
the bound is $P + (T(B + 1) + T + 2)$, where $P$ is the cost of the precomputation for $L$, $T$,
$H$ and $B$ is the cost of one iteration of the time loop for $L$, $N$, $T$, $H$.

A separate result bounds it by a constant depending only on $L$ and $N$ times $(T + H + 1)^6$. -/
def shBound (L : Layout) (N T H : ℕ) : ℕ := preB L T H + (T * (tBodyB L N T H + 1) + T + 2)

theorem encodeCNF_shFamily (T H : ℕ) :
    encodeCNF (shFamily L sa pl cn pu N T H) = (List.range T).flatMap (blkT L sa pl cn pu N T H) := by
  simp [encodeCNF, shFamily, List.flatMap_assoc]
  rfl

/-- **Correctness of the shift generator, with its explicit time bound.** Let $L$ be a layout, let
$\mathrm{sa}$, $\mathrm{pl}$, $\mathrm{cn}$, $\mathrm{pu}$ be situation tables and let
$N, T, H \in \mathbb{N}$, and suppose the tables are well formed for $N$ situations at height
$H$. Start the cell-shift generator for $L$, $\mathrm{sa}$, $\mathrm{pl}$, $\mathrm{cn}$,
$\mathrm{pu}$ and $N$ at its first precomputation stage, in state false, with $T$ on the counter
$\mathrm{Tn}$ and $H$ on the counter $\mathrm{Hs}$ in unary, all other counters empty, and an
arbitrary list $o$ of bits on the output stack. Then within at most the explicit time bound of
the shift generator for $L$, $N$, $T$, $H$ steps it reaches its final label $\mathrm{done}$, in
some state, with stacks whose output stack holds the encoding of the cell-shift clause family for
$L$, $\mathrm{sa}$, $\mathrm{pl}$, $\mathrm{cn}$, $\mathrm{pu}$, $N$, $T$ and $H$, followed by
$o$. -/
theorem sh_run (T H : ℕ) (hwf : WF L sa pl cn pu N H) (o : List Bool) :
    ∃ (v : Bool) (S : ∀ k, List (SΓ CK k)),
      RunLe (prog L sa pl cn pu N) (shBound L N T H)
        ⟨some (.pre .eg), false, st (initF T H) o⟩ ⟨some .done, v, S⟩ ∧
        S .out = encodeCNF (shFamily L sa pl cn pu N T H) ++ o := by
  refine ⟨false, st (preF L T H) (encodeCNF (shFamily L sa pl cn pu N T H) ++ o), ?_, rfl⟩
  refine Bud.start ?_
  refine (emitS (M := prog L sa pl cn pu N) (self := .pre .eg) (next := .pre (.hg .head)) (x := .Gc)
    rfl _ _ _).bud ?_
  refine (mulS_run (M := prog L sa pl cn pu N) (mk := fun s => .pre (.hg s)) (next := .pre .ew)
    (a := .Hs) (ad := .md) (b := .Gc) (c := .HG) (t := .tmp) (fun _ => rfl) (by decide) _
    (by simp [initF]) (by simp [initF]) _ _).bud ?_
  refine (emitS (M := prog L sa pl cn pu N) (self := .pre .ew) (next := .pre .ek) (x := .Wc) rfl _ _
    _).bud ?_
  refine (emitS (M := prog L sa pl cn pu N) (self := .pre .ek) (next := .pre (.w .head)) (x := .Ka)
    rfl _ _ _).bud ?_
  refine (mulS_run (M := prog L sa pl cn pu N) (mk := fun s => .pre (.w s)) (next := .pre .dk)
    (a := .Ka) (ad := .md) (b := .HG) (c := .Wc) (t := .tmp) (fun _ => rfl) (by decide) _
    (by simp [initF]) (by simp [initF]) _ _).bud ?_
  refine (drainS (M := prog L sa pl cn pu N) (self := .pre .dk) (next := .pre (.v .head)) (x := .Ka)
    rfl _ _ _).bud ?_
  refine (mulS_run (M := prog L sa pl cn pu N) (mk := fun s => .pre (.v s)) (next := .pre .vw1)
    (a := .Tn) (ad := .md) (b := .Wc) (c := .Vc) (t := .tmp) (fun _ => rfl) (by decide) _
    (by simp [initF]) (by simp [initF]) _ _).bud ?_
  refine (copyS (M := prog L sa pl cn pu N) (l₁ := .pre .vw1) (l₂ := .pre .vw2) (next := .tHead) rfl
    rfl (by decide) (by decide) (by decide) _ (by simp [initF]) _ _).bud ?_
  refine bud_st (F' := preF L T H) (by
    funext x; cases x <;> simp [initF, preF, Layout.rowW, Layout.numVars] <;> ring) ?_
  have hloop := stLoop (M := prog L sa pl cn pu N) (c := .Tn) (cd := .Ti) (head := .tHead)
    (body := .tw .head) (rest := .tRest) (next := .done) rfl rfl (by decide) T (tBodyB L N T H)
    (blkT L sa pl cn pu N T H) (preF L T H) rfl rfl
    (fun t ht o' => tbody_run ht hwf _
      ⟨by simp [preF], by simp [preF], by simp [preF], by simp [preF], by simp [preF]⟩
      (by simp [preF]) (by simp [preF]) (by simp [preF]) (by simp [preF]) (by simp [preF])
      (by simp [preF]) (by simp) (by simp [preF]) (by simp [preF]) (by simp [preF]) (by simp [preF])
      (by simp [preF]) (by simp [preF]) (by simp [preF]) (by simp [preF]) (by simp [preF])
      (by simp [preF]) o' true)
    false o
  rw [← encodeCNF_shFamily] at hloop
  refine hloop.bud (Bud.fin ?_ rfl)
  simp [initF, preB, shBound, Layout.rowW]
  ring_nf
  omega

end Top

/-! ## [BOUND] The time bound is polynomial: `shBound ≤ shC · (T + H + 1)^6` -/

section Poly

theorem shBound_mono {L L' : Layout} {N N' T T' H H' : ℕ} (hA : L.A ≤ L'.A) (hK : L.KK ≤ L'.KK)
    (hg : L.g ≤ L'.g) (hd : L.d ≤ L'.d) (hN : N ≤ N') (hT : T ≤ T') (hH : H ≤ H') :
    shBound L N T H ≤ shBound L' N' T' H' := by
  unfold shBound preB tBodyB ikB oBodyB sBodyB clauseB litE Layout.numVars Layout.rowW
  gcongr

/-- **Time bound of the shift generator on uniform layouts.** Let $k \ge 1$ and $y \ge 1$ be
natural numbers and let $L_k$ be the layout with every constant equal to $k$. Then the explicit
time bound of the shift generator for $L_k$ with $N = k$ situations and $T = H = y$ is at most
$828\, k^7 y^6$.

Every monomial of the bound is then at most $k^7 y^6$, and the coefficients sum to $828$, the
value of the bound at $k = y = 1$. -/
theorem shBound_uni (k y : ℕ) (hk : 1 ≤ k) (hy : 1 ≤ y) :
    shBound (Cslib.Complexity.CookLevin.Family.Layout.uni k) k y y ≤ 828 * k ^ 7 * y ^ 6 := by
  have m : ∀ a b, a ≤ 7 → b ≤ 6 → k ^ a * y ^ b ≤ k ^ 7 * y ^ 6 := fun a b ha hb =>
    Nat.mul_le_mul (Nat.pow_le_pow_right hk ha) (Nat.pow_le_pow_right hy hb)
  unfold shBound preB tBodyB ikB oBodyB sBodyB clauseB litE Layout.numVars Layout.rowW
    Cslib.Complexity.CookLevin.Family.Layout.uni
  simp only
  linarith [m 0 0 (by norm_num) (by norm_num),
    m 0 1 (by norm_num) (by norm_num),
    m 0 2 (by norm_num) (by norm_num),
    m 1 0 (by norm_num) (by norm_num),
    m 1 1 (by norm_num) (by norm_num),
    m 1 2 (by norm_num) (by norm_num),
    m 1 3 (by norm_num) (by norm_num),
    m 2 1 (by norm_num) (by norm_num),
    m 2 2 (by norm_num) (by norm_num),
    m 2 3 (by norm_num) (by norm_num),
    m 2 4 (by norm_num) (by norm_num),
    m 3 1 (by norm_num) (by norm_num),
    m 3 2 (by norm_num) (by norm_num),
    m 3 3 (by norm_num) (by norm_num),
    m 4 1 (by norm_num) (by norm_num),
    m 4 2 (by norm_num) (by norm_num),
    m 4 3 (by norm_num) (by norm_num),
    m 4 4 (by norm_num) (by norm_num),
    m 5 1 (by norm_num) (by norm_num),
    m 5 2 (by norm_num) (by norm_num),
    m 5 3 (by norm_num) (by norm_num),
    m 5 4 (by norm_num) (by norm_num),
    m 6 2 (by norm_num) (by norm_num),
    m 6 3 (by norm_num) (by norm_num),
    m 6 4 (by norm_num) (by norm_num),
    m 6 5 (by norm_num) (by norm_num),
    m 7 3 (by norm_num) (by norm_num),
    m 7 4 (by norm_num) (by norm_num),
    m 7 5 (by norm_num) (by norm_num),
    m 7 6 (by norm_num) (by norm_num)]

/-- **Constant of the shift-generator time bound.** For a layout $L$ with label/state block size
$A$, $K$ stacks, $g$ symbol codes and window depth $d$, and a natural number $N$, the constant is
$828 \cdot (A + K + g + d + N + 1)^7$.

It depends only on $A$, $K$, $g$, $d$ and $N$, not on the time bound $T$ or the height $H$. -/
def shC (L : Layout) (N : ℕ) : ℕ := 828 * (L.A + L.KK + L.g + L.d + N + 1) ^ 7

theorem shBound_le (L : Layout) (N T H : ℕ) : shBound L N T H ≤ shC L N * (T + H + 1) ^ 6 := by
  have := shBound_mono (L := L) (L' := Cslib.Complexity.CookLevin.Family.Layout.uni (L.A + L.KK + L.g + L.d + N + 1))
    (N := N) (N' := L.A + L.KK + L.g + L.d + N + 1) (T := T) (T' := T + H + 1) (H := H)
    (H' := T + H + 1)
    (by simp only [Cslib.Complexity.CookLevin.Family.Layout.uni]; omega) (by simp only [Cslib.Complexity.CookLevin.Family.Layout.uni]; omega)
    (by simp only [Cslib.Complexity.CookLevin.Family.Layout.uni]; omega) (by simp only [Cslib.Complexity.CookLevin.Family.Layout.uni]; omega)
    (by omega) (by omega) (by omega)
  have h2 := shBound_uni (L.A + L.KK + L.g + L.d + N + 1) (T + H + 1) (by omega) (by omega)
  unfold shC
  exact this.trans h2

open Polynomial in
/-- **The shift-generator time bound as a polynomial.** For a layout $L$ with label/state block
size $A$, $K$ stacks, $g$ symbol codes and window depth $d$, and a natural number $N$, let
$c = 828\,(A + K + g + d + N + 1)^7$ be the constant of the shift-generator time bound; this is
the polynomial $c\,(X + 1)^6$ with natural-number coefficients.

For natural numbers $T$ and $H$, its value at $X = T + H$ is $c\,(T + H + 1)^6$, the bound on
the number of steps of the shift generator started on $T$ and $H$. -/
noncomputable def shPoly (L : Layout) (N : ℕ) : Polynomial ℕ := C (shC L N) * (X + 1) ^ 6

theorem shPoly_eval (L : Layout) (N T H : ℕ) :
    (shPoly L N).eval (T + H) = shC L N * (T + H + 1) ^ 6 := by
  simp [shPoly]

/-- **Polynomial time bound for the shift generator.** Let $L$ be a layout with label/state block
size $A$, $K$ stacks, $g$ symbol codes and window depth $d$, let $\mathrm{sa}$, $\mathrm{pl}$,
$\mathrm{cn}$, $\mathrm{pu}$ be situation tables and let $N, T, H \in \mathbb{N}$, and suppose
the tables are well formed for $N$ situations at height $H$. Start the cell-shift generator for
$L$, $\mathrm{sa}$, $\mathrm{pl}$, $\mathrm{cn}$, $\mathrm{pu}$ and $N$ at its first
precomputation stage, in state false, with $T$ on the counter $\mathrm{Tn}$ and $H$ on the counter
$\mathrm{Hs}$ in unary, all other counters empty, and an arbitrary list $o$ of bits on the output
stack. Then within at most $c\,(T + H + 1)^6$ steps, where $c = 828\,(A + K + g + d + N + 1)^7$
is the constant of the shift-generator time bound for $L$ and $N$, it reaches its final label
$\mathrm{done}$, in some state, with stacks whose output stack holds the encoding of the
cell-shift clause family for $L$, $\mathrm{sa}$, $\mathrm{pl}$, $\mathrm{cn}$, $\mathrm{pu}$,
$N$, $T$ and $H$, followed by $o$. -/
theorem sh_time {L : Layout} {sa : ℕ → ℕ} {pl cn : ℕ → ℕ → ℕ} {pu : ℕ → ℕ → ℕ → ℕ} {N : ℕ}
    (T H : ℕ)
    (hwf : WF L sa pl cn pu N H) (o : List Bool) :
    ∃ (v : Bool) (S : ∀ k, List (SΓ CK k)),
      RunLe (prog L sa pl cn pu N) (shC L N * (T + H + 1) ^ 6)
        ⟨some (.pre .eg), false, st (initF T H) o⟩ ⟨some .done, v, S⟩ ∧
        S .out = encodeCNF (shFamily L sa pl cn pu N T H) ++ o :=
  let ⟨v, S, h, h'⟩ := sh_run T H hwf o; ⟨v, S, h.mono (shBound_le L N T H), h'⟩

end Poly

end Cslib.Complexity.CookLevin.Shift
