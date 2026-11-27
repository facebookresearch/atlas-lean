/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DynamicProgramming.SequenceAlignment
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Affine-gap pairwise sequence alignment: the Gotoh algorithm

Pairwise alignment with affine gap penalties (Gotoh, *An improved algorithm for
matching biological sequences*, J. Mol. Biol. 1982; Durbin et al., *Biological
Sequence Analysis*, Cambridge, 1998): opening a gap run costs `gapOpen`, extending
an already-open run costs `gapExtend` per column, so a run of `k ≥ 1` gap columns
costs `gapOpen + (k - 1) * gapExtend`. Linear-gap Needleman–Wunsch is the special
case `gapOpen = gapExtend = gap`.

The alignment score is a fold over the alignment columns carrying the previous
column's gap state; the dynamic program is a single fuel recursion carrying the
same state. The three continuation values are specializations of that program:
`gotohContNone` (previous column a match), `gotohContGapX` (previous column
a gap in `ys`), `gotohContGapY` (previous column a gap in `xs`).

These are continuation values, not endpoint-restricted Gotoh matrices: each is
the best score of a suffix alignment *given* the previous column, and the first
column of the remaining suffix alignment is unrestricted (it may be a match or
either gap). The previous state only prices the next gap, via `gapCost`.

Main results:

* `affineScore_le_gotohScore`, `exists_affineScore_eq_gotohScore`: **Gotoh is
  optimal**: every valid alignment scores at most `gotohScore`, and some alignment
  attains it.
* `gotohContNone_eq`, `gotohContGapX_eq`, `gotohContGapY_eq`: **first-column
  recurrences** for the three continuation values.
* `gotohScore_eq_nwScore`: with `gapOpen = gapExtend = gap`,
  affine-gap alignment is linear-gap Needleman–Wunsch.

Cost model: as with `nwScore` / `swCellScore`, the DP is an exponential-time
*specification*, not a memoized table; a tabulated `O(|xs| * |ys|)` implementation
proved equal to it is future work.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean

universe u

variable {α : Type u}

/-- **Gap states.** A gap state is one of three values: $\mathrm{none}$, $\mathrm{gapX}$ and
$\mathrm{gapY}$. The affine-gap score and the Gotoh recursion carry one as the kind of the previous
column: $\mathrm{gapX}$ after a column pairing an element of the first sequence with a gap,
$\mathrm{gapY}$ after a column pairing a gap with an element of the second sequence, and
$\mathrm{none}$ otherwise, including before the first column. -/
inductive GapState | none | gapX | gapY deriving DecidableEq, Repr

/-- **Gap cost.** Given an integer gap-open cost $o$, an integer gap-extend cost $e$ and gap states
$p$ (of the previous column) and $c$ (of the current gap column), the cost of the current column
is $e$ if $p = c$ (the column continues a run) and $o$ otherwise (it opens a run). -/
def gapCost (gapOpen gapExtend : ℤ) (prev cur : GapState) : ℤ :=
  if prev = cur then gapExtend else gapOpen

section Affine

variable (σ : α → α → ℤ) (gapOpen gapExtend : ℤ)

/-- **Affine-gap score from a gap state.** Fix an integer substitution score $\sigma$, an integer
gap-open cost $o$ and an integer gap-extend cost $e$. The affine-gap score of an alignment started
from a gap state $p$ is the sum of its column scores, computed left to right while carrying a gap
state that starts at $p$ and is updated after each column. The empty alignment scores $0$. A
column pairing an element $a$ of the first sequence with an element $b$ of the second scores
$\sigma(a, b)$ and sets the state to $\mathrm{none}$. A column pairing an element of the first
sequence with a gap has kind $\mathrm{gapX}$, and a column pairing a gap with an element of the
second sequence has kind $\mathrm{gapY}$; such a column scores $e$ if the carried state equals its
kind and $o$ otherwise, and sets the state to its kind. A column of two gaps scores $0$ and sets
the state to $\mathrm{none}$.

The column of two gaps cannot occur in a valid alignment; it is scored as a no-op. -/
def affineScoreAux : Alignment α → GapState → ℤ
  | [], _ => 0
  | (some a, some b) :: A, _ => σ a b + affineScoreAux A .none
  | (some _, none) :: A, prev =>
      gapCost gapOpen gapExtend prev .gapX + affineScoreAux A .gapX
  | (none, some _) :: A, prev =>
      gapCost gapOpen gapExtend prev .gapY + affineScoreAux A .gapY
  | (none, none) :: A, _ => affineScoreAux A .none

/-- **Affine-gap alignment score.** Given an integer substitution score $\sigma$, an integer
gap-open cost $o$ and an integer gap-extend cost $e$, the affine-gap score of an alignment is its
affine-gap score from a gap state, started from the state $\mathrm{none}$ (no open gap run). -/
def affineScore (A : Alignment α) : ℤ := affineScoreAux σ gapOpen gapExtend A .none

/-- **Fuel-bounded Gotoh recursion.** Fix an integer-valued scoring function $\sigma$ on pairs of
letters and integer gap-open and gap-extend penalties $g_o$ and $g_e$. A gap state records what
the previous alignment column was: a match ($\mathrm{none}$), a gap in the second sequence
($\mathrm{gapX}$) or a gap in the first sequence ($\mathrm{gapY}$). For gap states $p$, $q$ let
$c(p, q)$ be the gap cost, $g_e$ if $p = q$ and $g_o$ otherwise. Write $\varepsilon$ for the
empty sequence and $a \cdot u$ for the sequence with first letter $a$ followed by $u$. For fuel
$n \in \mathbb{N}$, sequences $u$, $v$ and a gap state $p$, the integer $G_n(u, v, p)$ is defined
by recursion on $n$: $G_0(u, v, p) = 0$, $G_{n+1}(\varepsilon, \varepsilon, p) = 0$,
$G_{n+1}(\varepsilon, b \cdot v, p) = c(p, \mathrm{gapY}) + G_n(\varepsilon, v, \mathrm{gapY})$,
$G_{n+1}(a \cdot u, \varepsilon, p) = c(p, \mathrm{gapX}) + G_n(u, \varepsilon, \mathrm{gapX})$,
and $G_{n+1}(a \cdot u, b \cdot v, p)$ is the maximum of $\sigma(a, b) + G_n(u, v, \mathrm{none})$,
$c(p, \mathrm{gapX}) + G_n(u, b \cdot v, \mathrm{gapX})$ and
$c(p, \mathrm{gapY}) + G_n(a \cdot u, v, \mathrm{gapY})$.

With fuel at least the sum of the two lengths this is the Gotoh dynamic program; with less fuel
the base case $G_0 = 0$ cuts the recursion short. -/
def gotohAux : ℕ → List α → List α → GapState → ℤ
  | 0, _, _, _ => 0
  | _ + 1, [], [], _ => 0
  | n + 1, [], b :: ys, prev => gapCost gapOpen gapExtend prev .gapY + gotohAux n [] ys .gapY
  | n + 1, a :: xs, [], prev => gapCost gapOpen gapExtend prev .gapX + gotohAux n xs [] .gapX
  | n + 1, a :: xs, b :: ys, prev =>
      max (σ a b + gotohAux n xs ys .none)
        (max (gapCost gapOpen gapExtend prev .gapX + gotohAux n xs (b :: ys) .gapX)
          (gapCost gapOpen gapExtend prev .gapY + gotohAux n (a :: xs) ys .gapY))

/-- **Gotoh value with no open gap run.** Given a substitution score $\sigma$, a gap-open score
$g_o$ and a gap-extend score $g_e$, this is the value of the Gotoh dynamic program on sequences
$x$ and $y$ when no gap run is open (the previous column was a match, or there is no previous
column): the best affine-gap score of an alignment of $x$ and $y$, where a match column pairing
$a$ with $b$ scores $\sigma(a, b)$ and a gap column scores $g_e$ if it continues a run of gaps in
the same sequence and $g_o$ otherwise.

It is a continuation value, not an endpoint-restricted matrix: the first column may be a match
or either gap. -/
def gotohContNone (xs ys : List α) : ℤ :=
  gotohAux σ gapOpen gapExtend (xs.length + ys.length) xs ys .none

/-- **Gotoh continuation value after a gap in the second sequence.** Fix an integer-valued
scoring function $\sigma$ on pairs of letters and integer gap-open and gap-extend penalties $g_o$
and $g_e$. For sequences $u$ and $v$, the value $X(u, v)$ is the fuel-bounded Gotoh recursion on
$u$ and $v$, run with fuel equal to the sum of their lengths and started in the gap state where
the previous column was a gap in $v$.

It is the best affine-gap score of an alignment of $u$ with $v$ scored from that state. It is a
continuation value, not an endpoint-restricted matrix: the next column may be a match or either
gap, and the previous state only makes a next gap in $v$ cost $g_e$ instead of $g_o$. -/
def gotohContGapX (xs ys : List α) : ℤ :=
  gotohAux σ gapOpen gapExtend (xs.length + ys.length) xs ys .gapX

/-- **Gotoh continuation value after a gap in the first sequence.** Fix an integer-valued
scoring function $\sigma$ on pairs of letters and integer gap-open and gap-extend penalties $g_o$
and $g_e$. For sequences $u$ and $v$, the value $Y(u, v)$ is the fuel-bounded Gotoh recursion on
$u$ and $v$, run with fuel equal to the sum of their lengths and started in the gap state where
the previous column was a gap in $u$.

It is the best affine-gap score of an alignment of $u$ with $v$ scored from that state. It is a
continuation value, not an endpoint-restricted matrix: the next column may be a match or either
gap, and the previous state only makes a next gap in $u$ cost $g_e$ instead of $g_o$. -/
def gotohContGapY (xs ys : List α) : ℤ :=
  gotohAux σ gapOpen gapExtend (xs.length + ys.length) xs ys .gapY

/-- **Gotoh score.** For a substitution score $\sigma$ and gap-open and gap-extend scores $g_o$
and $g_e$, the Gotoh score of sequences $x$ and $y$ is the Gotoh value of $x$ against $y$ with no
open gap run, since no gap run is open before the first column.

It is the optimal affine-gap alignment score of $x$ and $y$. -/
def gotohScore (xs ys : List α) : ℤ := gotohContNone σ gapOpen gapExtend xs ys

/-- Extra fuel does not change the DP. -/
private theorem gotohAux_succ_of_le : ∀ (m : ℕ) (xs ys : List α) (prev : GapState),
    xs.length + ys.length ≤ m →
    gotohAux σ gapOpen gapExtend m xs ys prev =
      gotohAux σ gapOpen gapExtend (m + 1) xs ys prev
  | 0, xs, ys, _, h => by
      have hx : xs = [] := List.length_eq_zero_iff.mp (by omega)
      have hy : ys = [] := List.length_eq_zero_iff.mp (by omega)
      subst hx
      subst hy
      rfl
  | m + 1, [], [], _, _ => rfl
  | m + 1, [], b :: ys, _, _ => by
      have h2 : (b :: ys).length = ys.length + 1 := rfl
      simp only [gotohAux]
      rw [gotohAux_succ_of_le m [] ys .gapY (by omega)]
  | m + 1, a :: xs, [], _, _ => by
      have h1 : (a :: xs).length = xs.length + 1 := rfl
      simp only [gotohAux]
      rw [gotohAux_succ_of_le m xs [] .gapX (by omega)]
  | m + 1, a :: xs, b :: ys, prev, _ => by
      have h1 : (a :: xs).length = xs.length + 1 := rfl
      have h2 : (b :: ys).length = ys.length + 1 := rfl
      simp only [gotohAux]
      rw [gotohAux_succ_of_le m xs ys .none (by omega),
        gotohAux_succ_of_le m xs (b :: ys) .gapX (by omega),
        gotohAux_succ_of_le m (a :: xs) ys .gapY (by omega)]

/-- The DP depends only on the lengths through the fuel bound. -/
private theorem gotohAux_eq_of_le (m : ℕ) (xs ys : List α) (prev : GapState)
    (h : xs.length + ys.length ≤ m) :
    gotohAux σ gapOpen gapExtend m xs ys prev =
      gotohAux σ gapOpen gapExtend (xs.length + ys.length) xs ys prev := by
  induction m, h using Nat.le_induction with
  | base => rfl
  | succ m hm ih =>
      rw [← ih, gotohAux_succ_of_le σ gapOpen gapExtend m xs ys prev hm]

/-- **Cost of a gap run.** Given an integer gap-open cost $o$, an integer gap-extend cost $e$, gap
states $p$ (of the column before the run) and $c$ (of the run's columns) and a length
$k \in \mathbb{N}$, the cost of a run of $k$ gap columns is $k e$ if $p = c$ (the run continues
an open run); otherwise it is $0$ for $k = 0$ and $o + (k - 1) e$ for $k \ge 1$. -/
def gapRunCost (gapOpen gapExtend : ℤ) (prev cur : GapState) (k : ℕ) : ℤ :=
  if prev = cur then (k : ℤ) * gapExtend
  else if k = 0 then 0 else gapOpen + ((k - 1 : ℕ) : ℤ) * gapExtend

/-- **Adding a column to a gap run.** For an integer gap-open cost $o$, an integer gap-extend cost
$e$, gap states $p$ and $c$ and $k \in \mathbb{N}$, the gap cost of a column in state $c$ after
state $p$, plus the cost of a run of $k$ columns in state $c$ that follows state $c$, equals the
cost of a run of $k + 1$ columns in state $c$ that follows state $p$. -/
theorem gapRunCost_succ (gapOpen gapExtend : ℤ) (prev cur : GapState) (k : ℕ) :
    gapCost gapOpen gapExtend prev cur + gapRunCost gapOpen gapExtend cur cur k
      = gapRunCost gapOpen gapExtend prev cur (k + 1) := by
  by_cases hprev : prev = cur
  · subst hprev
    simp [gapCost, gapRunCost]
    ring
  · have hne : ¬ (k + 1 = 0) := by omega
    simp [gapCost, gapRunCost, hprev, hne]

/-- Aligning `[]` against `ys` is a single gap run in `ys`. -/
private theorem gotohAux_nil_left : ∀ (m : ℕ) (ys : List α) (prev : GapState),
    ys.length ≤ m →
    gotohAux σ gapOpen gapExtend m [] ys prev =
      gapRunCost gapOpen gapExtend prev .gapY ys.length := by
  intro m
  induction m with
  | zero =>
      intro ys prev hle
      have hy : ys = [] := List.length_eq_zero_iff.mp (by omega)
      subst hy
      simp [gotohAux, gapRunCost]
  | succ m ih =>
      intro ys prev hle
      cases ys with
      | nil => simp [gotohAux, gapRunCost]
      | cons b ys =>
          have hlen : (b :: ys).length = ys.length + 1 := rfl
          have hstep : gotohAux σ gapOpen gapExtend (m + 1) [] (b :: ys) prev =
              gapCost gapOpen gapExtend prev .gapY +
                gotohAux σ gapOpen gapExtend m [] ys .gapY := rfl
          rw [hstep, ih ys .gapY (by omega)]
          exact gapRunCost_succ gapOpen gapExtend prev .gapY ys.length

/-- Aligning `xs` against `[]` is a single gap run in `xs`. -/
private theorem gotohAux_nil_right : ∀ (m : ℕ) (xs : List α) (prev : GapState),
    xs.length ≤ m →
    gotohAux σ gapOpen gapExtend m xs [] prev =
      gapRunCost gapOpen gapExtend prev .gapX xs.length := by
  intro m
  induction m with
  | zero =>
      intro xs prev hle
      have hx : xs = [] := List.length_eq_zero_iff.mp (by omega)
      subst hx
      simp [gotohAux, gapRunCost]
  | succ m ih =>
      intro xs prev hle
      cases xs with
      | nil => simp [gotohAux, gapRunCost]
      | cons a xs =>
          have hlen : (a :: xs).length = xs.length + 1 := rfl
          have hstep : gotohAux σ gapOpen gapExtend (m + 1) (a :: xs) [] prev =
              gapCost gapOpen gapExtend prev .gapX +
                gotohAux σ gapOpen gapExtend m xs [] .gapX := rfl
          rw [hstep, ih xs .gapX (by omega)]
          exact gapRunCost_succ gapOpen gapExtend prev .gapX xs.length

/-- **Removing a leading match column from a valid alignment.** Let $a$ and $b$ be elements,
let $xs$ and $ys$ be sequences, and let $A$ be an alignment. If the alignment whose first column
is the match column $(a, b)$, followed by the columns of $A$, is a valid alignment of the
sequence $a$ followed by $xs$ and the sequence $b$ followed by $ys$, then $A$ is a valid
alignment of $xs$ and $ys$. -/
theorem isAlignment_of_cons_match {a b : α} {A : Alignment α} {xs ys : List α}
    (h : IsAlignment ((some a, some b) :: A) (a :: xs) (b :: ys)) : IsAlignment A xs ys := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun c hc => h1 c (List.mem_cons_of_mem _ hc), ?_, ?_⟩
  · have h2' := h2
    rw [List.filterMap_cons] at h2'
    simpa using h2'
  · have h3' := h3
    rw [List.filterMap_cons] at h3'
    simpa using h3'

/-- **Removing a leading column with a gap in the second sequence.** Let $A$ be an alignment, $a$
an element and $x$, $y$ sequences. If prepending to $A$ the column that pairs $a$ with a gap gives
a valid alignment of $a x$ (the sequence $x$ with $a$ prepended) and $y$, then $A$ is a valid
alignment of $x$ and $y$. -/
theorem isAlignment_of_cons_gapX {a : α} {A : Alignment α} {xs ys : List α}
    (h : IsAlignment ((some a, none) :: A) (a :: xs) ys) : IsAlignment A xs ys := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun c hc => h1 c (List.mem_cons_of_mem _ hc), ?_, ?_⟩
  · have h2' := h2
    rw [List.filterMap_cons] at h2'
    simpa using h2'
  · have h3' := h3
    rw [List.filterMap_cons] at h3'
    simpa using h3'

/-- **Removing a leading column with a gap in the first sequence.** Let $A$ be an alignment, $b$
an element and $x$, $y$ sequences. If prepending to $A$ the column that pairs a gap with $b$ gives
a valid alignment of $x$ and $b y$ (the sequence $y$ with $b$ prepended), then $A$ is a valid
alignment of $x$ and $y$. -/
theorem isAlignment_of_cons_gapY {b : α} {A : Alignment α} {xs ys : List α}
    (h : IsAlignment ((none, some b) :: A) xs (b :: ys)) : IsAlignment A xs ys := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun c hc => h1 c (List.mem_cons_of_mem _ hc), ?_, ?_⟩
  · have h2' := h2
    rw [List.filterMap_cons] at h2'
    simpa using h2'
  · have h3' := h3
    rw [List.filterMap_cons] at h3'
    simpa using h3'

/-- **Prepending a match column.** If $A$ is a valid alignment of sequences $x$ and $y$, then for
all elements $a$ and $b$, the alignment obtained by prepending to $A$ the column that pairs $a$
with $b$ is a valid alignment of $a x$ and $b y$ (the sequences $x$ and $y$ with $a$ and $b$
prepended). -/
theorem isAlignment_cons_match {a b : α} {A : Alignment α} {xs ys : List α}
    (h : IsAlignment A xs ys) : IsAlignment ((some a, some b) :: A) (a :: xs) (b :: ys) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · simp
    · exact h1 c hc
  · simp [List.filterMap_cons, h2]
  · simp [List.filterMap_cons, h3]

/-- **Prepending a column with a gap in the second sequence.** If $A$ is a valid alignment of
sequences $x$ and $y$, then for every element $a$, the alignment obtained by prepending to $A$ the
column that pairs $a$ with a gap is a valid alignment of $a x$ (the sequence $x$ with $a$
prepended) and $y$. -/
theorem isAlignment_cons_gapX {a : α} {A : Alignment α} {xs ys : List α}
    (h : IsAlignment A xs ys) : IsAlignment ((some a, none) :: A) (a :: xs) ys := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · simp
    · exact h1 c hc
  · simp [List.filterMap_cons, h2]
  · simp [List.filterMap_cons, h3]

/-- **Prepending a column with a gap in the first sequence.** If $A$ is a valid alignment of
sequences $x$ and $y$, then for every element $b$, the alignment obtained by prepending to $A$ the
column that pairs a gap with $b$ is a valid alignment of $x$ and $b y$ (the sequence $y$ with $b$
prepended). -/
theorem isAlignment_cons_gapY {b : α} {A : Alignment α} {xs ys : List α}
    (h : IsAlignment A xs ys) : IsAlignment ((none, some b) :: A) xs (b :: ys) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · simp
    · exact h1 c hc
  · simp [List.filterMap_cons, h2]
  · simp [List.filterMap_cons, h3]

/-- One DP step on two nonempty sequences, in terms of the three continuation values. -/
private theorem gotohAux_cons_cons (a b : α) (xs ys : List α) (prev : GapState) :
    gotohAux σ gapOpen gapExtend ((a :: xs).length + (b :: ys).length) (a :: xs) (b :: ys)
        prev =
      max (σ a b + gotohContNone σ gapOpen gapExtend xs ys)
        (max (gapCost gapOpen gapExtend prev .gapX + gotohContGapX σ gapOpen gapExtend xs (b :: ys))
          (gapCost gapOpen gapExtend prev .gapY +
            gotohContGapY σ gapOpen gapExtend (a :: xs) ys)) := by
  have hfuel : (a :: xs).length + (b :: ys).length = (xs.length + ys.length + 1) + 1 := by
    simp only [List.length_cons]
    omega
  rw [hfuel]
  simp only [gotohAux]
  rw [← gotohAux_succ_of_le σ gapOpen gapExtend (xs.length + ys.length) xs ys .none le_rfl]
  have h3 : gotohAux σ gapOpen gapExtend (xs.length + ys.length + 1) (a :: xs) ys .gapY
      = gotohContGapY σ gapOpen gapExtend (a :: xs) ys := by
    rw [gotohAux_eq_of_le σ gapOpen gapExtend (xs.length + ys.length + 1) (a :: xs) ys .gapY
      (by simp only [List.length_cons]; omega)]
    rfl
  rw [h3]
  congr 1

/-- One DP step when the second sequence is empty. -/
private theorem gotohAux_cons_nil (a : α) (xs : List α) (prev : GapState) :
    gotohAux σ gapOpen gapExtend ((a :: xs).length + ([] : List α).length) (a :: xs)
        ([] : List α) prev =
      gapCost gapOpen gapExtend prev .gapX + gotohContGapX σ gapOpen gapExtend xs [] := by
  have hfuel : (a :: xs).length + ([] : List α).length = xs.length + 1 := by simp
  rw [hfuel]
  simp only [gotohAux]
  rfl

/-- One DP step when the first sequence is empty. -/
private theorem gotohAux_nil_cons (b : α) (ys : List α) (prev : GapState) :
    gotohAux σ gapOpen gapExtend (([] : List α).length + (b :: ys).length) ([] : List α)
        (b :: ys) prev =
      gapCost gapOpen gapExtend prev .gapY + gotohContGapY σ gapOpen gapExtend [] ys := by
  have hfuel : ([] : List α).length + (b :: ys).length = ys.length + 1 := by simp
  rw [hfuel]
  simp only [gotohAux]
  rw [show gotohContGapY σ gapOpen gapExtend [] ys
      = gotohAux σ gapOpen gapExtend (0 + ys.length) [] ys .gapY from rfl]
  rw [Nat.zero_add]

/-- **Gotoh is optimal** (general previous state): every valid alignment scores at
most the DP. -/
private theorem affineScoreAux_le_gotohAux : ∀ (A : Alignment α) (xs ys : List α) (prev : GapState),
    IsAlignment A xs ys →
    affineScoreAux σ gapOpen gapExtend A prev ≤
      gotohAux σ gapOpen gapExtend (xs.length + ys.length) xs ys prev := by
  intro A
  induction A with
  | nil =>
      intro xs ys prev h
      obtain ⟨h1, h2, h3⟩ := h
      have hx : xs = [] := h2.symm
      have hy : ys = [] := h3.symm
      subst hx
      subst hy
      simp [affineScoreAux, gotohAux]
  | cons c A' ih =>
      intro xs ys prev h
      obtain ⟨c1, c2⟩ := c
      cases c1 with
      | none =>
          cases c2 with
          | none => exact absurd rfl (h.1 _ List.mem_cons_self)
          | some b =>
              -- Head column is `(none, some b)`: it consumes `b` from `ys` only.
              have hy : ys = b :: A'.filterMap Prod.snd := by
                simpa [List.filterMap_cons] using h.2.2.symm
              subst hy
              cases xs with
              | nil =>
                  have hA' := isAlignment_of_cons_gapY h
                  have hIH := ih _ _ .gapY hA'
                  rw [gotohAux_nil_cons]
                  show gapCost gapOpen gapExtend prev .gapY +
                      affineScoreAux σ gapOpen gapExtend A' .gapY ≤ _
                  exact le_trans (add_le_add_right hIH (gapCost gapOpen gapExtend prev .gapY))
                    le_rfl
              | cons a xs =>
                  have hA' := isAlignment_of_cons_gapY h
                  have hIH := ih _ _ .gapY hA'
                  rw [gotohAux_cons_cons]
                  show gapCost gapOpen gapExtend prev .gapY +
                      affineScoreAux σ gapOpen gapExtend A' .gapY ≤ _
                  exact le_trans (add_le_add_right hIH (gapCost gapOpen gapExtend prev .gapY))
                    (le_max_of_le_right (le_max_of_le_right le_rfl))
      | some a =>
          cases c2 with
          | none =>
              -- Head column is `(some a, none)`: it consumes `a` from `xs` only.
              have hx : xs = a :: A'.filterMap Prod.fst := by
                simpa [List.filterMap_cons] using h.2.1.symm
              subst hx
              cases ys with
              | nil =>
                  have hA' := isAlignment_of_cons_gapX h
                  have hIH := ih _ _ .gapX hA'
                  rw [gotohAux_cons_nil]
                  show gapCost gapOpen gapExtend prev .gapX +
                      affineScoreAux σ gapOpen gapExtend A' .gapX ≤ _
                  exact le_trans (add_le_add_right hIH (gapCost gapOpen gapExtend prev .gapX))
                    le_rfl
              | cons b ys =>
                  have hA' := isAlignment_of_cons_gapX h
                  have hIH := ih _ _ .gapX hA'
                  rw [gotohAux_cons_cons]
                  show gapCost gapOpen gapExtend prev .gapX +
                      affineScoreAux σ gapOpen gapExtend A' .gapX ≤ _
                  exact le_trans (add_le_add_right hIH (gapCost gapOpen gapExtend prev .gapX))
                    (le_max_of_le_right (le_max_of_le_left le_rfl))
          | some b =>
              have hx : xs = a :: A'.filterMap Prod.fst := by
                simpa [List.filterMap_cons] using h.2.1.symm
              have hy : ys = b :: A'.filterMap Prod.snd := by
                simpa [List.filterMap_cons] using h.2.2.symm
              subst hx
              subst hy
              have hA' := isAlignment_of_cons_match h
              have hIH := ih _ _ .none hA'
              rw [gotohAux_cons_cons]
              show σ a b + affineScoreAux σ gapOpen gapExtend A' .none ≤ _
              exact le_trans (add_le_add_right hIH (σ a b)) (le_max_of_le_left le_rfl)

/-- **Gotoh is attained**: some valid alignment achieves the DP. -/
private theorem exists_affineScore_eq_gotohAux : ∀ (n : ℕ) (xs ys : List α) (prev : GapState),
    xs.length + ys.length ≤ n →
    ∃ A, IsAlignment A xs ys ∧ affineScoreAux σ gapOpen gapExtend A prev =
      gotohAux σ gapOpen gapExtend n xs ys prev := by
  intro n
  induction n with
  | zero =>
      intro xs ys prev hle
      have hx : xs = [] := List.length_eq_zero_iff.mp (by omega)
      have hy : ys = [] := List.length_eq_zero_iff.mp (by omega)
      subst hx
      subst hy
      exact ⟨[], ⟨by simp, rfl, rfl⟩, by simp [affineScoreAux, gotohAux]⟩
  | succ n ih =>
      intro xs ys prev hle
      cases xs with
      | nil =>
          cases ys with
          | nil =>
              exact ⟨[], ⟨by simp, rfl, rfl⟩, by simp [affineScoreAux, gotohAux]⟩
          | cons b ys =>
              obtain ⟨A', hA', hscore⟩ := ih [] ys .gapY
                (by have h1 : (b :: ys).length = ys.length + 1 := rfl; omega)
              refine ⟨(none, some b) :: A', isAlignment_cons_gapY hA', ?_⟩
              show gapCost gapOpen gapExtend prev .gapY +
                  affineScoreAux σ gapOpen gapExtend A' .gapY = _
              rw [hscore]
              simp only [gotohAux]
      | cons a xs =>
          cases ys with
          | nil =>
              obtain ⟨A', hA', hscore⟩ := ih xs [] .gapX
                (by have h1 : (a :: xs).length = xs.length + 1 := rfl; omega)
              refine ⟨(some a, none) :: A', isAlignment_cons_gapX hA', ?_⟩
              show gapCost gapOpen gapExtend prev .gapX +
                  affineScoreAux σ gapOpen gapExtend A' .gapX = _
              rw [hscore]
              simp only [gotohAux]
          | cons b ys =>
              have hlen1 : (a :: xs).length = xs.length + 1 := rfl
              have hlen2 : (b :: ys).length = ys.length + 1 := rfl
              obtain ⟨A1, hA1, hs1⟩ := ih xs ys .none (by omega)
              obtain ⟨A2, hA2, hs2⟩ := ih xs (b :: ys) .gapX (by omega)
              obtain ⟨A3, hA3, hs3⟩ := ih (a :: xs) ys .gapY (by omega)
              simp only [gotohAux]
              rcases le_total
                  (σ a b + gotohAux σ gapOpen gapExtend n xs ys .none)
                  (max (gapCost gapOpen gapExtend prev .gapX +
                    gotohAux σ gapOpen gapExtend n xs (b :: ys) .gapX)
                    (gapCost gapOpen gapExtend prev .gapY +
                      gotohAux σ gapOpen gapExtend n (a :: xs) ys .gapY)) with hmax | hmax
              · rw [max_eq_right hmax]
                rcases le_total
                    (gapCost gapOpen gapExtend prev .gapX +
                      gotohAux σ gapOpen gapExtend n xs (b :: ys) .gapX)
                    (gapCost gapOpen gapExtend prev .gapY +
                      gotohAux σ gapOpen gapExtend n (a :: xs) ys .gapY) with h2 | h2
                · rw [max_eq_right h2]
                  refine ⟨(none, some b) :: A3, isAlignment_cons_gapY hA3, ?_⟩
                  show gapCost gapOpen gapExtend prev .gapY +
                      affineScoreAux σ gapOpen gapExtend A3 .gapY = _
                  rw [hs3]
                · rw [max_eq_left h2]
                  refine ⟨(some a, none) :: A2, isAlignment_cons_gapX hA2, ?_⟩
                  show gapCost gapOpen gapExtend prev .gapX +
                      affineScoreAux σ gapOpen gapExtend A2 .gapX = _
                  rw [hs2]
              · rw [max_eq_left hmax]
                refine ⟨(some a, some b) :: A1, isAlignment_cons_match hA1, ?_⟩
                show σ a b + affineScoreAux σ gapOpen gapExtend A1 .none =
                  σ a b + gotohAux σ gapOpen gapExtend n xs ys .none
                rw [hs1]

/-- **Gotoh is optimal.** Let $\sigma$ be an integer substitution score, $o$ an integer gap-open
cost and $e$ an integer gap-extend cost. For all sequences $x$ and $y$ and every valid alignment
$A$ of $x$ and $y$, the affine-gap score of $A$ is at most the Gotoh score of $x$ and $y$, both
taken with $\sigma$, $o$ and $e$. -/
theorem affineScore_le_gotohScore (A : Alignment α) (xs ys : List α)
    (hA : IsAlignment A xs ys) :
    affineScore σ gapOpen gapExtend A ≤ gotohScore σ gapOpen gapExtend xs ys :=
  affineScoreAux_le_gotohAux σ gapOpen gapExtend A xs ys .none hA

/-- **Gotoh is attained.** Let $\sigma$ be an integer substitution score, $o$ an integer gap-open
cost and $e$ an integer gap-extend cost. For all sequences $x$ and $y$ there is a valid alignment
$A$ of $x$ and $y$ whose affine-gap score equals the Gotoh score of $x$ and $y$, both taken with
$\sigma$, $o$ and $e$. -/
theorem exists_affineScore_eq_gotohScore (xs ys : List α) :
    ∃ A, IsAlignment A xs ys ∧
      affineScore σ gapOpen gapExtend A = gotohScore σ gapOpen gapExtend xs ys := by
  obtain ⟨A, hA, hscore⟩ := exists_affineScore_eq_gotohAux σ gapOpen gapExtend
    (xs.length + ys.length) xs ys .none le_rfl
  exact ⟨A, hA, hscore⟩

/-- **First-column recurrence for the continuation after a match.** Fix an
integer-valued scoring function $\sigma$ on pairs of letters and integer gap-open and gap-extend
penalties $g_o$ and $g_e$. For sequences $u$, $v$ let $N(u, v)$, $X(u, v)$ and $Y(u, v)$ be the
Gotoh continuation values when the previous column was a match, a gap in $v$ and a gap in $u$
respectively, and write $a \cdot u$ for the sequence with first letter $a$ followed by $u$. For
all letters $a$, $b$ and sequences $u$, $v$, the value $N(a \cdot u, b \cdot v)$ is the maximum
of $N(u, v) + \sigma(a, b)$, $X(u, b \cdot v) + g_o$ and $Y(a \cdot u, v) + g_o$. -/
theorem gotohContNone_eq (a b : α) (xs ys : List α) :
    gotohContNone σ gapOpen gapExtend (a :: xs) (b :: ys) =
      max (gotohContNone σ gapOpen gapExtend xs ys + σ a b)
        (max (gotohContGapX σ gapOpen gapExtend xs (b :: ys) + gapOpen)
          (gotohContGapY σ gapOpen gapExtend (a :: xs) ys + gapOpen)) := by
  show gotohAux σ gapOpen gapExtend ((a :: xs).length + (b :: ys).length) (a :: xs) (b :: ys)
      .none = _
  rw [gotohAux_cons_cons]
  have hg1 : gapCost gapOpen gapExtend .none .gapX = gapOpen := by simp [gapCost]
  have hg2 : gapCost gapOpen gapExtend .none .gapY = gapOpen := by simp [gapCost]
  rw [hg1, hg2, add_comm (σ a b) (gotohContNone σ gapOpen gapExtend xs ys),
    add_comm gapOpen (gotohContGapX σ gapOpen gapExtend xs (b :: ys)),
    add_comm gapOpen (gotohContGapY σ gapOpen gapExtend (a :: xs) ys)]

/-- **First-column recurrence for the continuation after a gap in the second sequence.** Fix an
integer-valued scoring function $\sigma$ on pairs of letters and integer gap-open and gap-extend
penalties $g_o$ and $g_e$. For sequences $u$, $v$ let $N(u, v)$, $X(u, v)$ and $Y(u, v)$ be the
Gotoh continuation values when the previous column was a match, a gap in $v$ and a gap in $u$
respectively, and write $a \cdot u$ for the sequence with first letter $a$ followed by $u$. For
all letters $a$, $b$ and sequences $u$, $v$, the value $X(a \cdot u, b \cdot v)$ is the maximum
of $N(u, v) + \sigma(a, b)$, $X(u, b \cdot v) + g_e$ and $Y(a \cdot u, v) + g_o$. -/
theorem gotohContGapX_eq (a b : α) (xs ys : List α) :
    gotohContGapX σ gapOpen gapExtend (a :: xs) (b :: ys) =
      max (gotohContNone σ gapOpen gapExtend xs ys + σ a b)
        (max (gotohContGapX σ gapOpen gapExtend xs (b :: ys) + gapExtend)
          (gotohContGapY σ gapOpen gapExtend (a :: xs) ys + gapOpen)) := by
  show gotohAux σ gapOpen gapExtend ((a :: xs).length + (b :: ys).length) (a :: xs) (b :: ys)
      .gapX = _
  rw [gotohAux_cons_cons]
  have hg1 : gapCost gapOpen gapExtend .gapX .gapX = gapExtend := by simp [gapCost]
  have hg2 : gapCost gapOpen gapExtend .gapX .gapY = gapOpen := by simp [gapCost]
  rw [hg1, hg2, add_comm (σ a b) (gotohContNone σ gapOpen gapExtend xs ys),
    add_comm gapExtend (gotohContGapX σ gapOpen gapExtend xs (b :: ys)),
    add_comm gapOpen (gotohContGapY σ gapOpen gapExtend (a :: xs) ys)]

/-- **First-column recurrence for the continuation after a gap in the first sequence.** Fix an
integer-valued scoring function $\sigma$ on pairs of letters and integer gap-open and gap-extend
penalties $g_o$ and $g_e$. For sequences $u$, $v$ let $N(u, v)$, $X(u, v)$ and $Y(u, v)$ be the
Gotoh continuation values when the previous column was a match, a gap in $v$ and a gap in $u$
respectively, and write $a \cdot u$ for the sequence with first letter $a$ followed by $u$. For
all letters $a$, $b$ and sequences $u$, $v$, the value $Y(a \cdot u, b \cdot v)$ is the maximum
of $N(u, v) + \sigma(a, b)$, $X(u, b \cdot v) + g_o$ and $Y(a \cdot u, v) + g_e$. -/
theorem gotohContGapY_eq (a b : α) (xs ys : List α) :
    gotohContGapY σ gapOpen gapExtend (a :: xs) (b :: ys) =
      max (gotohContNone σ gapOpen gapExtend xs ys + σ a b)
        (max (gotohContGapX σ gapOpen gapExtend xs (b :: ys) + gapOpen)
          (gotohContGapY σ gapOpen gapExtend (a :: xs) ys + gapExtend)) := by
  show gotohAux σ gapOpen gapExtend ((a :: xs).length + (b :: ys).length) (a :: xs) (b :: ys)
      .gapY = _
  rw [gotohAux_cons_cons]
  have hg1 : gapCost gapOpen gapExtend .gapY .gapX = gapOpen := by simp [gapCost]
  have hg2 : gapCost gapOpen gapExtend .gapY .gapY = gapExtend := by simp [gapCost]
  rw [hg1, hg2, add_comm (σ a b) (gotohContNone σ gapOpen gapExtend xs ys),
    add_comm gapOpen (gotohContGapX σ gapOpen gapExtend xs (b :: ys)),
    add_comm gapExtend (gotohContGapY σ gapOpen gapExtend (a :: xs) ys)]

/-- **Gotoh value against an empty first sequence.** Let $g_o$ and $g_e$ be the gap-open and
gap-extend scores. For every sequence $y$ of length $n$, the Gotoh value with no open gap run of
the empty sequence against $y$ equals the score of a freshly opened run of $n$ gaps in the first
sequence: $0$ if $n = 0$, and $g_o + (n - 1) g_e$ if $n \ge 1$. -/
theorem gotohContNone_nil_left (ys : List α) :
    gotohContNone σ gapOpen gapExtend [] ys =
      gapRunCost gapOpen gapExtend .none .gapY ys.length :=
  gotohAux_nil_left σ gapOpen gapExtend (([] : List α).length + ys.length) ys .none (by simp)

/-- **Gotoh value against an empty second sequence.** Let $g_o$ and $g_e$ be the gap-open and
gap-extend scores. For every sequence $x$ of length $n$, the Gotoh value with no open gap run of
$x$ against the empty sequence equals the score of a freshly opened run of $n$ gaps in the second
sequence: $0$ if $n = 0$, and $g_o + (n - 1) g_e$ if $n \ge 1$. -/
theorem gotohContNone_nil_right (xs : List α) :
    gotohContNone σ gapOpen gapExtend xs [] =
      gapRunCost gapOpen gapExtend .none .gapX xs.length :=
  gotohAux_nil_right σ gapOpen gapExtend (xs.length + ([] : List α).length) xs .none (by simp)

/-- **Continuation after a gap in the second sequence, empty first sequence.** Fix a scoring
function $\sigma$ on pairs of letters and integer gap-open and gap-extend penalties $g_o$ and
$g_e$, and let $X(u, v)$ be the Gotoh continuation value of sequences $u$, $v$ when the previous
column was a gap in $v$. For every sequence $v$ of length $k$, the value $X(\varepsilon, v)$,
where $\varepsilon$ is the empty sequence, is the cost of one freshly opened gap run of length
$k$: it is $0$ if $k = 0$ and $g_o + (k - 1) g_e$ if $k \ge 1$. -/
theorem gotohContGapX_nil_left (ys : List α) :
    gotohContGapX σ gapOpen gapExtend [] ys =
      gapRunCost gapOpen gapExtend .gapX .gapY ys.length :=
  gotohAux_nil_left σ gapOpen gapExtend (([] : List α).length + ys.length) ys .gapX (by simp)

/-- **Continuation after a gap in the second sequence, empty second sequence.** Fix a scoring
function $\sigma$ on pairs of letters and integer gap-open and gap-extend penalties $g_o$ and
$g_e$, and let $X(u, v)$ be the Gotoh continuation value of sequences $u$, $v$ when the previous
column was a gap in $v$. For every sequence $u$ of length $k$, the value $X(u, \varepsilon)$,
where $\varepsilon$ is the empty sequence, equals $k \, g_e$: the open gap run is extended by
$k$ columns. -/
theorem gotohContGapX_nil_right (xs : List α) :
    gotohContGapX σ gapOpen gapExtend xs [] =
      gapRunCost gapOpen gapExtend .gapX .gapX xs.length :=
  gotohAux_nil_right σ gapOpen gapExtend (xs.length + ([] : List α).length) xs .gapX (by simp)

/-- **Continuation after a gap in the first sequence, empty first sequence.** Fix a scoring
function $\sigma$ on pairs of letters and integer gap-open and gap-extend penalties $g_o$ and
$g_e$, and let $Y(u, v)$ be the Gotoh continuation value of sequences $u$, $v$ when the previous
column was a gap in $u$. For every sequence $v$ of length $k$, the value $Y(\varepsilon, v)$,
where $\varepsilon$ is the empty sequence, equals $k \, g_e$: the open gap run is extended by
$k$ columns. -/
theorem gotohContGapY_nil_left (ys : List α) :
    gotohContGapY σ gapOpen gapExtend [] ys =
      gapRunCost gapOpen gapExtend .gapY .gapY ys.length :=
  gotohAux_nil_left σ gapOpen gapExtend (([] : List α).length + ys.length) ys .gapY (by simp)

/-- **Continuation after a gap in the first sequence, empty second sequence.** Fix a scoring
function $\sigma$ on pairs of letters and integer gap-open and gap-extend penalties $g_o$ and
$g_e$, and let $Y(u, v)$ be the Gotoh continuation value of sequences $u$, $v$ when the previous
column was a gap in $u$. For every sequence $u$ of length $k$, the value $Y(u, \varepsilon)$,
where $\varepsilon$ is the empty sequence, is the cost of one freshly opened gap run of length
$k$: it is $0$ if $k = 0$ and $g_o + (k - 1) g_e$ if $k \ge 1$. -/
theorem gotohContGapY_nil_right (xs : List α) :
    gotohContGapY σ gapOpen gapExtend xs [] =
      gapRunCost gapOpen gapExtend .gapY .gapX xs.length :=
  gotohAux_nil_right σ gapOpen gapExtend (xs.length + ([] : List α).length) xs .gapY (by simp)

/-- **Linear gaps as affine gaps, from any gap state.** Let $\sigma$ be an integer substitution
score and $g$ an integer. If the gap-open cost and the gap-extend cost both equal $g$, then for
every alignment $A$ and every gap state $p$, the affine-gap score of $A$ started from state $p$,
with substitution score $\sigma$, equals the alignment score of $A$ with substitution score
$\sigma$ and gap penalty $g$. -/
theorem affineScoreAux_eq_alignmentScore (gap : ℤ) (hopen : gapOpen = gap)
    (hext : gapExtend = gap) : ∀ (A : Alignment α) (prev : GapState),
    affineScoreAux σ gapOpen gapExtend A prev = alignmentScore σ gap A := by
  intro A
  induction A with
  | nil => intro prev; rfl
  | cons c A' ih =>
      intro prev
      have hg : ∀ cur : GapState, gapCost gapOpen gapExtend prev cur = gap := by
        intro cur
        by_cases h : prev = cur
        · subst h; simp [gapCost, hext]
        · simp [gapCost, h, hopen]
      obtain ⟨c1, c2⟩ := c
      cases c1 with
      | none =>
          cases c2 with
          | none =>
              show affineScoreAux σ gapOpen gapExtend A' .none =
                alignmentScore σ gap ((none, none) :: A')
              rw [ih .none]
              simp [alignmentScore, columnScore]
          | some b =>
              show gapCost gapOpen gapExtend prev .gapY +
                  affineScoreAux σ gapOpen gapExtend A' .gapY =
                alignmentScore σ gap ((none, some b) :: A')
              rw [ih .gapY, hg .gapY]
              simp [alignmentScore, columnScore]
      | some a =>
          cases c2 with
          | none =>
              show gapCost gapOpen gapExtend prev .gapX +
                  affineScoreAux σ gapOpen gapExtend A' .gapX =
                alignmentScore σ gap ((some a, none) :: A')
              rw [ih .gapX, hg .gapX]
              simp [alignmentScore, columnScore]
          | some b =>
              show σ a b + affineScoreAux σ gapOpen gapExtend A' .none =
                alignmentScore σ gap ((some a, some b) :: A')
              rw [ih .none]
              simp [alignmentScore, columnScore]

/-- **Linear gaps are affine gaps with equal costs.** Let $\sigma$ be an integer substitution
score and $g$ an integer. If the gap-open cost and the gap-extend cost both equal $g$, then for
every alignment $A$, the affine-gap score of $A$ with substitution score $\sigma$ equals the
alignment score of $A$ with substitution score $\sigma$ and gap penalty $g$. -/
theorem affineScore_eq_alignmentScore (gap : ℤ) (hopen : gapOpen = gap)
    (hext : gapExtend = gap) (A : Alignment α) :
    affineScore σ gapOpen gapExtend A = alignmentScore σ gap A :=
  affineScoreAux_eq_alignmentScore σ gapOpen gapExtend gap hopen hext A .none

/-- **Gotoh with equal gap scores is Needleman–Wunsch.** Let $\sigma$ be a substitution score
and $g$ an integer. If the gap-open and gap-extend scores both equal $g$, then for all sequences
$x$ and $y$ the Gotoh score (optimal affine-gap alignment score) of $x$ and $y$ equals the
Needleman–Wunsch score of $x$ and $y$ with substitution score $\sigma$ and gap score $g$. -/
theorem gotohScore_eq_nwScore (gap : ℤ) (hopen : gapOpen = gap) (hext : gapExtend = gap)
    (xs ys : List α) :
    gotohScore σ gapOpen gapExtend xs ys = nwScore σ gap xs ys := by
  apply le_antisymm
  · obtain ⟨A, hA, hscore⟩ := exists_affineScore_eq_gotohScore σ gapOpen gapExtend xs ys
    rw [← hscore, affineScore_eq_alignmentScore σ gapOpen gapExtend gap hopen hext A]
    exact alignmentScore_le_nwScore σ gap xs ys A hA
  · obtain ⟨A, hA, hscore⟩ := exists_alignmentScore_eq_nwScore σ gap xs ys
    rw [← hscore, ← affineScore_eq_alignmentScore σ gapOpen gapExtend gap hopen hext A]
    exact affineScore_le_gotohScore σ gapOpen gapExtend A xs ys hA

end Affine

end Cslib.Algorithms.Lean
