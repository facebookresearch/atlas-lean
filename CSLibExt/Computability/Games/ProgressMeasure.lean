/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Small progress measures for parity games: a costed verifier
-/
module

public import CSLibExt.Computability.Games.Encoded
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Card

/-!
# Small progress measures for parity games: a costed verifier

Jurdziński's *small progress measures* certify the even player's winning region of a finite
parity game: a map `μ` assigning to each position a tuple of length `d + 1` (plus a top element
`none`, for positions losing for the even player), such that along every edge the tuple does not
increase in the *truncated lexicographic* order at the priority of the edge's tail, and strictly
decreases there when the priority is odd. The truncated order at priority `p` compares the suffix
`p, p + 1, …, d` lexicographically from the top (largest priority) downwards: the first component
where the two tuples differ, scanning from `d` down to `p`, decides, and components below `p` are
ignored. In particular, components above `p` need not agree: a larger higher component outweighs
any difference below it.

This file gives the verifier on encoded games (`EncodedParityGame`: owner as a `Bool`, moves as a
`Bool` matrix, priorities as `ℕ → ℕ`), so it is a concrete computable function, not an existential
Boolean.

* `lexGtTrunc`, `lexGeTrunc`: the strict and non-strict truncated lexicographic orders.
* `progCheck`: the progress condition for one edge; `verifyProgress`: at every even position some
  successor satisfies it, at every odd position every successor does.
* `costedVerifyProgress`: the verifier together with the number of atomic component comparisons it
  actually evaluates, built from costed Boolean combinators (`costedAnd`, `costedOr`,
  `costedAll`, `costedAny`). Proved: its result is `verifyProgress`
  (`costedVerifyProgress_fst`) and its cost is at most `verifyProgressCostBound n d`
  (`costedVerifyProgress_cost_le`), a polynomial in `n + d`; with priorities compressed to at most
  `2 n` (`EncodedParityGame.priorityCompress`) this is `O(n ^ 4)`.

That the positions with such certificates are exactly the winning positions, and hence that
parity games are in NP ∩ coNP, is deferred: `parity_games_np_inter_coNP_wanted` in
`WantedExt.TheoryOfComputation.ParityGameComplexityWanted`.
-/

@[expose] public section

namespace Cslib.Games.ProgressMeasure

/-- The strict truncated lexicographic order at priority `p`: `a >_p b`
iff, scanning components from `d` down to `p`, the first component where
`a` and `b` differ has `a` strictly larger. Components below `p` are
ignored. Source: M. Jurdziński, "Small progress measures for solving parity
games", *Proceedings of STACS 2000*, LNCS 1770, 290-301. -/
def lexGtTrunc {d : ℕ} (p : ℕ) (a b : Fin (d + 1) → ℕ) : Bool :=
  (List.finRange (d + 1)).any fun j =>
    decide (p ≤ j.val) && decide (b j < a j) &&
      (List.finRange (d + 1)).all fun i =>
        (!decide (j.val < i.val) || decide (a i = b i))

/-- The non-strict truncated lexicographic order at priority `p`:
`a ≥_p b` iff `a >_p b` or `a` and `b` agree on every component at
least `p`. Source: M. Jurdziński, "Small progress measures for solving
parity games", *Proceedings of STACS 2000*, LNCS 1770, 290-301. -/
def lexGeTrunc {d : ℕ} (p : ℕ) (a b : Fin (d + 1) → ℕ) : Bool :=
  lexGtTrunc p a b ||
    (List.finRange (d + 1)).all fun i =>
      (!decide (p ≤ i.val) || decide (a i = b i))

/-- The progress-measure condition for the edge `v → w`: at even
priority of `v` the tuple must not increase in the truncated lexicographic
order at that priority, at odd priority it must strictly decrease. The
top element `none` at `v` satisfies every comparison (a losing position
imposes no progress requirement); a finite tuple at `v` never satisfies
the condition against `none` at `w`, since `none` is the top element.
Source: M. Jurdziński, "Small progress measures for solving parity games",
*Proceedings of STACS 2000*, LNCS 1770, 290-301. -/
def progCheck {n d : ℕ} (G : EncodedParityGame n)
    (μ : Fin n → Option (Fin (d + 1) → ℕ)) (v w : Fin n) : Bool :=
  match μ v, μ w with
  | none, _ => true
  | some _, none => false
  | some a, some b =>
    if G.priority v % 2 = 0 then lexGeTrunc (G.priority v) a b
    else lexGtTrunc (G.priority v) a b

/-- **The progress-measure verifier.** It accepts `μ` when, at every even
position, some successor satisfies the progress condition, and at every odd
position, every successor does. This is a concrete computable function: a
bounded loop over positions, successors, and tuple components. Source:
M. Jurdziński, "Small progress measures for solving parity games",
*Proceedings of STACS 2000*, LNCS 1770, 290-301. -/
def verifyProgress {n d : ℕ} (G : EncodedParityGame n)
    (μ : Fin n → Option (Fin (d + 1) → ℕ)) : Bool :=
  (List.finRange n).all fun v =>
    if G.owner v then
      (List.finRange n).all fun w => (!G.move v w) || progCheck G μ v w
    else
      (List.finRange n).any fun w => G.move v w && progCheck G μ v w

/-- Boolean AND on costed results: the result is the AND of the results
and the cost is the sum of the costs, so every subcomputation's cost is
counted exactly once. Source: M. Jurdziński, "Small progress measures for
solving parity games", *Proceedings of STACS 2000*, LNCS 1770, 290-301. -/
def costedAnd (a b : Bool × ℕ) : Bool × ℕ := (a.1 && b.1, a.2 + b.2)

/-- Boolean OR on costed results: the result is the OR of the results
and the cost is the sum of the costs. Source: M. Jurdziński, "Small
progress measures for solving parity games", *Proceedings of STACS 2000*,
LNCS 1770, 290-301. -/
def costedOr (a b : Bool × ℕ) : Bool × ℕ := (a.1 || b.1, a.2 + b.2)

/-- The result of `costedAnd` is the AND of the results. Source:
M. Jurdziński, "Small progress measures for solving parity games",
*Proceedings of STACS 2000*, LNCS 1770, 290-301. -/
@[simp] theorem costedAnd_fst (a b : Bool × ℕ) :
    (costedAnd a b).1 = (a.1 && b.1) := rfl

/-- The result of `costedOr` is the OR of the results. Source:
M. Jurdziński, "Small progress measures for solving parity games",
*Proceedings of STACS 2000*, LNCS 1770, 290-301. -/
@[simp] theorem costedOr_fst (a b : Bool × ℕ) :
    (costedOr a b).1 = (a.1 || b.1) := rfl

/-- The cost of `costedAnd` is the sum of the costs. Source:
M. Jurdziński, "Small progress measures for solving parity games",
*Proceedings of STACS 2000*, LNCS 1770, 290-301. -/
@[simp] theorem costedAnd_snd (a b : Bool × ℕ) :
    (costedAnd a b).2 = (a.2 + b.2) := rfl

/-- The cost of `costedOr` is the sum of the costs. Source:
M. Jurdziński, "Small progress measures for solving parity games",
*Proceedings of STACS 2000*, LNCS 1770, 290-301. -/
@[simp] theorem costedOr_snd (a b : Bool × ℕ) :
    (costedOr a b).2 = (a.2 + b.2) := rfl

/-- Costed conjunction over a list: evaluate `f` on every element (no
short-circuit), AND the results, sum the costs. Source: M. Jurdziński,
"Small progress measures for solving parity games", *Proceedings of STACS
2000*, LNCS 1770, 290-301. -/
def costedAll {α : Type} (l : List α) (f : α → Bool × ℕ) : Bool × ℕ :=
  match l with
  | [] => (true, 0)
  | x :: xs => costedAnd (f x) (costedAll xs f)

/-- Costed disjunction over a list: evaluate `f` on every element (no
short-circuit), OR the results, sum the costs. Source: M. Jurdziński,
"Small progress measures for solving parity games", *Proceedings of STACS
2000*, LNCS 1770, 290-301. -/
def costedAny {α : Type} (l : List α) (f : α → Bool × ℕ) : Bool × ℕ :=
  match l with
  | [] => (false, 0)
  | x :: xs => costedOr (f x) (costedAny xs f)

/-- The result of `costedAll` is the `List.all` of the component results.
Source: M. Jurdziński, "Small progress measures for solving parity games",
*Proceedings of STACS 2000*, LNCS 1770, 290-301. -/
theorem costedAll_fst {α : Type} (l : List α) (f : α → Bool × ℕ) :
    (costedAll l f).1 = l.all fun x => (f x).1 := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [costedAll, List.all, ih]

/-- The result of `costedAny` is the `List.any` of the component results.
Source: M. Jurdziński, "Small progress measures for solving parity games",
*Proceedings of STACS 2000*, LNCS 1770, 290-301. -/
theorem costedAny_fst {α : Type} (l : List α) (f : α → Bool × ℕ) :
    (costedAny l f).1 = l.any fun x => (f x).1 := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [costedAny, List.any, ih]

/-- If every component costs at most `C`, the costed conjunction costs at
most `l.length * C`. Source: M. Jurdziński, "Small progress measures for
solving parity games", *Proceedings of STACS 2000*, LNCS 1770, 290-301. -/
theorem costedAll_cost_le {α : Type} {l : List α} {f : α → Bool × ℕ} {C : ℕ}
    (h : ∀ x ∈ l, (f x).2 ≤ C) : (costedAll l f).2 ≤ l.length * C := by
  induction l with
  | nil => simp [costedAll]
  | cons x xs ih =>
    have hx : (f x).2 ≤ C := h x (by simp)
    have hxs : ∀ y ∈ xs, (f y).2 ≤ C := fun y hy => h y (List.mem_cons_of_mem _ hy)
    have ih' := ih hxs
    simp only [costedAll, costedAnd_snd, List.length_cons, Nat.succ_mul]
    omega

/-- If every component costs at most `C`, the costed disjunction costs at
most `l.length * C`. Source: M. Jurdziński, "Small progress measures for
solving parity games", *Proceedings of STACS 2000*, LNCS 1770, 290-301. -/
theorem costedAny_cost_le {α : Type} {l : List α} {f : α → Bool × ℕ} {C : ℕ}
    (h : ∀ x ∈ l, (f x).2 ≤ C) : (costedAny l f).2 ≤ l.length * C := by
  induction l with
  | nil => simp [costedAny]
  | cons x xs ih =>
    have hx : (f x).2 ≤ C := h x (by simp)
    have hxs : ∀ y ∈ xs, (f y).2 ≤ C := fun y hy => h y (List.mem_cons_of_mem _ hy)
    have ih' := ih hxs
    simp only [costedAny, costedOr_snd, List.length_cons, Nat.succ_mul]
    omega

/-- The costed strict truncated lexicographic order: the same comparisons
as `lexGtTrunc`, with each atomic comparison costing `1`. Source:
M. Jurdziński, "Small progress measures for solving parity games",
*Proceedings of STACS 2000*, LNCS 1770, 290-301. -/
def costedLexGtTrunc {d : ℕ} (p : ℕ) (a b : Fin (d + 1) → ℕ) : Bool × ℕ :=
  costedAny (List.finRange (d + 1)) fun j =>
    costedAnd (costedAnd ((decide (p ≤ j.val), 1)) ((decide (b j < a j), 1)))
      (costedAll (List.finRange (d + 1)) fun i =>
        costedOr ((!(decide (j.val < i.val)), 1)) ((decide (a i = b i), 1)))

/-- The costed non-strict truncated lexicographic order: the same
comparisons as `lexGeTrunc`, with each atomic comparison costing `1`.
Source: M. Jurdziński, "Small progress measures for solving parity games",
*Proceedings of STACS 2000*, LNCS 1770, 290-301. -/
def costedLexGeTrunc {d : ℕ} (p : ℕ) (a b : Fin (d + 1) → ℕ) : Bool × ℕ :=
  costedOr (costedLexGtTrunc p a b)
    (costedAll (List.finRange (d + 1)) fun i =>
      costedOr ((!(decide (p ≤ i.val)), 1)) ((decide (a i = b i), 1)))

/-- The costed strict truncated order has the same result as `lexGtTrunc`.
Source: M. Jurdziński, "Small progress measures for solving parity games",
*Proceedings of STACS 2000*, LNCS 1770, 290-301. -/
theorem costedLexGtTrunc_fst {d : ℕ} (p : ℕ) (a b : Fin (d + 1) → ℕ) :
    (costedLexGtTrunc p a b).1 = lexGtTrunc p a b := by
  unfold costedLexGtTrunc lexGtTrunc
  rw [costedAny_fst]
  congr 1
  funext j
  simp [costedAll_fst]

/-- The costed strict truncated order costs at most `(d + 1) * (2 + (d + 1) * 2)`:
for each of the `d + 1` candidate first-differing components, two atomic
comparisons plus one inner scan of `d + 1` pairs of atomic comparisons.
Source: M. Jurdziński, "Small progress measures for solving parity games",
*Proceedings of STACS 2000*, LNCS 1770, 290-301. -/
theorem costedLexGtTrunc_cost_le {d : ℕ} (p : ℕ) (a b : Fin (d + 1) → ℕ) :
    (costedLexGtTrunc p a b).2 ≤ (d + 1) * (2 + (d + 1) * 2) := by
  have hInner : ∀ j : Fin (d + 1),
      (costedAll (List.finRange (d + 1)) fun i =>
        costedOr ((!(decide (j.val < i.val)), 1)) ((decide (a i = b i), 1))).2 ≤
        (d + 1) * 2 := by
    intro j
    have h := costedAll_cost_le (l := List.finRange (d + 1))
      (f := fun i => costedOr ((!(decide (j.val < i.val)), 1))
        ((decide (a i = b i), 1))) (C := 2) (by intro i _; simp [costedOr])
    simpa [List.length_finRange] using h
  have h := costedAny_cost_le (l := List.finRange (d + 1))
    (f := fun j => costedAnd (costedAnd ((decide (p ≤ j.val), 1))
      ((decide (b j < a j), 1)))
      (costedAll (List.finRange (d + 1)) fun i =>
        costedOr ((!(decide (j.val < i.val)), 1)) ((decide (a i = b i), 1))))
    (C := 2 + (d + 1) * 2) (by
      intro j _
      have hij := hInner j
      simp only [costedAnd_snd]
      omega)
  simpa [costedLexGtTrunc, List.length_finRange] using h

/-- The costed non-strict truncated order has the same result as `lexGeTrunc`.
Source: M. Jurdziński, "Small progress measures for solving parity games",
*Proceedings of STACS 2000*, LNCS 1770, 290-301. -/
theorem costedLexGeTrunc_fst {d : ℕ} (p : ℕ) (a b : Fin (d + 1) → ℕ) :
    (costedLexGeTrunc p a b).1 = lexGeTrunc p a b := by
  simp [costedLexGeTrunc, lexGeTrunc, costedLexGtTrunc_fst, costedAll_fst]

/-- The per-edge cost bound for `costedProgCheck`: the strict-order bound
plus one inner scan of `d + 1` pairs of atomic comparisons for the
non-strict case. Source: M. Jurdziński, "Small progress measures for
solving parity games", *Proceedings of STACS 2000*, LNCS 1770, 290-301. -/
def progCheckCostBound (d : ℕ) : ℕ := (d + 1) * (2 + (d + 1) * 2) + (d + 1) * 2

/-- The costed non-strict truncated order costs at most
`progCheckCostBound d`. Source: M. Jurdziński, "Small progress measures
for solving parity games", *Proceedings of STACS 2000*, LNCS 1770, 290-301. -/
theorem costedLexGeTrunc_cost_le {d : ℕ} (p : ℕ) (a b : Fin (d + 1) → ℕ) :
    (costedLexGeTrunc p a b).2 ≤ progCheckCostBound d := by
  have hGt := costedLexGtTrunc_cost_le p a b
  have hAll : (costedAll (List.finRange (d + 1)) fun i =>
      costedOr ((!(decide (p ≤ i.val)), 1)) ((decide (a i = b i), 1))).2 ≤
      (d + 1) * 2 := by
    have h := costedAll_cost_le (l := List.finRange (d + 1))
      (f := fun i => costedOr ((!(decide (p ≤ i.val)), 1))
        ((decide (a i = b i), 1))) (C := 2) (by intro i _; simp [costedOr])
    simpa [List.length_finRange] using h
  unfold costedLexGeTrunc progCheckCostBound
  simp only [costedOr_snd]
  omega

/-- The costed progress-measure condition for the edge `v → w`: the same
comparisons as `progCheck`, with each atomic comparison costing `1`.
Source: M. Jurdziński, "Small progress measures for solving parity games",
*Proceedings of STACS 2000*, LNCS 1770, 290-301. -/
def costedProgCheck {n d : ℕ} (G : EncodedParityGame n)
    (μ : Fin n → Option (Fin (d + 1) → ℕ)) (v w : Fin n) : Bool × ℕ :=
  match μ v, μ w with
  | none, _ => (true, 0)
  | some _, none => (false, 0)
  | some a, some b =>
    if G.priority v % 2 = 0 then costedLexGeTrunc (G.priority v) a b
    else costedLexGtTrunc (G.priority v) a b

/-- The costed edge check has the same result as `progCheck`. Source:
M. Jurdziński, "Small progress measures for solving parity games",
*Proceedings of STACS 2000*, LNCS 1770, 290-301. -/
theorem costedProgCheck_fst {n d : ℕ} (G : EncodedParityGame n)
    (μ : Fin n → Option (Fin (d + 1) → ℕ)) (v w : Fin n) :
    (costedProgCheck G μ v w).1 = progCheck G μ v w := by
  cases hv : μ v with
  | none => simp [costedProgCheck, progCheck, hv]
  | some a =>
    cases hw : μ w with
    | none => simp [costedProgCheck, progCheck, hv, hw]
    | some b =>
      by_cases hpar : G.priority v % 2 = 0
      · simp [costedProgCheck, progCheck, hv, hw, hpar, costedLexGeTrunc_fst]
      · simp [costedProgCheck, progCheck, hv, hw, hpar, costedLexGtTrunc_fst]

/-- The costed edge check costs at most `progCheckCostBound d`. Source:
M. Jurdziński, "Small progress measures for solving parity games",
*Proceedings of STACS 2000*, LNCS 1770, 290-301. -/
theorem costedProgCheck_cost_le {n d : ℕ} (G : EncodedParityGame n)
    (μ : Fin n → Option (Fin (d + 1) → ℕ)) (v w : Fin n) :
    (costedProgCheck G μ v w).2 ≤ progCheckCostBound d := by
  cases hv : μ v with
  | none => simp [costedProgCheck, hv]
  | some a =>
    cases hw : μ w with
    | none => simp [costedProgCheck, hv, hw]
    | some b =>
      simp only [costedProgCheck, hv, hw]
      by_cases hpar : G.priority v % 2 = 0
      · rw [ite_eq_left hpar]
        exact costedLexGeTrunc_cost_le _ _ _
      · rw [ite_eq_right hpar]
        have hGt := costedLexGtTrunc_cost_le (G.priority v) a b
        unfold progCheckCostBound
        omega

/-- The total cost bound for the costed verifier: at most `n` positions,
each with at most `n` successors, each edge costing one move test plus at
most `progCheckCostBound d`. Source: M. Jurdziński, "Small progress
measures for solving parity games", *Proceedings of STACS 2000*,
LNCS 1770, 290-301. -/
def verifyProgressCostBound (n d : ℕ) : ℕ :=
  n * (n * (1 + progCheckCostBound d))

/-- **The costed progress-measure verifier.** It computes the same result
as `verifyProgress`, together with the number of atomic component
comparisons (plus one move test per edge) it actually evaluates: the
traversal that computes the result is the traversal that accumulates the
cost, so the cost is not a separately computed cardinality. Source:
M. Jurdziński, "Small progress measures for solving parity games",
*Proceedings of STACS 2000*, LNCS 1770, 290-301. -/
def costedVerifyProgress {n d : ℕ} (G : EncodedParityGame n)
    (μ : Fin n → Option (Fin (d + 1) → ℕ)) : Bool × ℕ :=
  costedAll (List.finRange n) fun v =>
    if G.owner v then
      costedAll (List.finRange n) fun w =>
        costedOr ((!(G.move v w), 1)) (costedProgCheck G μ v w)
    else
      costedAny (List.finRange n) fun w =>
        costedAnd ((G.move v w, 1)) (costedProgCheck G μ v w)

/-- The costed verifier has the same result as `verifyProgress`. Source:
M. Jurdziński, "Small progress measures for solving parity games",
*Proceedings of STACS 2000*, LNCS 1770, 290-301. -/
theorem costedVerifyProgress_fst {n d : ℕ} (G : EncodedParityGame n)
    (μ : Fin n → Option (Fin (d + 1) → ℕ)) :
    (costedVerifyProgress G μ).1 = verifyProgress G μ := by
  unfold costedVerifyProgress verifyProgress
  rw [costedAll_fst]
  congr 1
  funext v
  by_cases hov : G.owner v = true
  · rw [ite_eq_left hov, ite_eq_left hov, costedAll_fst]
    congr 1
    funext w
    simp [costedProgCheck_fst]
  · rw [ite_eq_right hov, ite_eq_right hov, costedAny_fst]
    congr 1
    funext w
    simp [costedProgCheck_fst]

/-- The costed verifier costs at most `verifyProgressCostBound n d`,
a polynomial in `n + d`; on the priority-compressed game (`d = 2 * n`)
this is `O(n ^ 4)` in `n` alone. Source: M. Jurdziński, "Small progress
measures for solving parity games", *Proceedings of STACS 2000*,
LNCS 1770, 290-301. -/
theorem costedVerifyProgress_cost_le {n d : ℕ} (G : EncodedParityGame n)
    (μ : Fin n → Option (Fin (d + 1) → ℕ)) :
    (costedVerifyProgress G μ).2 ≤ verifyProgressCostBound n d := by
  have h := costedAll_cost_le (l := List.finRange n)
    (f := fun v => if G.owner v then
      costedAll (List.finRange n) fun w =>
        costedOr ((!(G.move v w), 1)) (costedProgCheck G μ v w)
    else
      costedAny (List.finRange n) fun w =>
        costedAnd ((G.move v w, 1)) (costedProgCheck G μ v w))
    (C := n * (1 + progCheckCostBound d)) (by
      intro v _
      by_cases hov : G.owner v = true
      · rw [ite_eq_left hov]
        have h2 := costedAll_cost_le (l := List.finRange n)
          (f := fun w => costedOr ((!(G.move v w), 1)) (costedProgCheck G μ v w))
          (C := 1 + progCheckCostBound d) (by
            intro w _
            have hP := costedProgCheck_cost_le G μ v w
            simp only [costedOr_snd]
            omega)
        simpa [List.length_finRange] using h2
      · rw [ite_eq_right hov]
        have h2 := costedAny_cost_le (l := List.finRange n)
          (f := fun w => costedAnd ((G.move v w, 1)) (costedProgCheck G μ v w))
          (C := 1 + progCheckCostBound d) (by
            intro w _
            have hP := costedProgCheck_cost_le G μ v w
            simp only [costedAnd_snd]
            omega)
        simpa [List.length_finRange] using h2)
  simpa [costedVerifyProgress, verifyProgressCostBound, List.length_finRange]
    using h

end Cslib.Games.ProgressMeasure
