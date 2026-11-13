/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Square products of disjoint blocks of consecutive integers (Erdős Problem 363)

Erdős Problem 363: are there only finitely many collections of disjoint intervals `I₁, …, Iₙ` of
integers with `|Iᵢ| ≥ 4` such that `∏ᵢ ∏_{m ∈ Iᵢ} m` is a square?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Even
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

namespace MathlibExt.NumberTheory.SquareProductDisjointIntervalsErdosProblem363Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #363, https://www.erdosproblems.com/363 (status
DISPROVED (LEAN)). UnsolvedMath record UM-30006839 (`EP-363`), dataset ulamai/UnsolvedMath v1.8.0.

Intervals consist of positive integers (an interval containing `0` has product `0`, a square). The
claim is stated for each fixed number `n` of intervals and fixed sizes `k₁, …, kₙ ≥ 4`, as in
formal-conjectures (without fixing them, finiteness already fails by a result of Skałba); it implies
the version over all `n`, so its refutation is the stronger statement. Collections are lists of
`Finset.Icc` intervals. Compared with the formal-conjectures statement `ErdosProblems/363.lean`
(equivalent, with positivity of the intervals built into the predicate; no code imported).
-/

/-- `S` is a list of pairwise disjoint intervals `[a, b]` of positive integers whose sizes are the
entries of `ks` and whose elements multiply to a perfect square. -/
def IsSquareIntervalCollection (ks : List ℕ) (S : List (Finset ℕ)) : Prop :=
  (∀ I ∈ S, ∃ a b : ℕ, 0 < a ∧ I = Finset.Icc a b) ∧ S.Pairwise Disjoint ∧
    S.map Finset.card = ks ∧ IsSquare (S.map fun I => ∏ m ∈ I, m).prod

/-- Erdős Problem 363: for every number `n` of intervals and all sizes `k₁, …, kₙ ≥ 4`, only
finitely many collections of disjoint intervals of positive integers of these sizes have a square
product. -/
def finitelyManySquareIntervalProducts : Prop :=
  ∀ ks : List ℕ, (∀ k ∈ ks, 4 ≤ k) →
    {S : List (Finset ℕ) | IsSquareIntervalCollection ks S}.Finite

/--
Resolved false: Ulas constructed infinitely many collections of four disjoint blocks of four
consecutive positive integers whose product is a square (and likewise for every `n ≥ 6` blocks of
size 4); Bauer and Bennett did `n = 3, 5`, and Bennett and Van Luijk found infinitely many for `n ≥
5` blocks of size 5. erdosproblems.com/363 lists the problem as disproved. Source: T. F. Bloom,
Erdős Problems, Problem #363, https://www.erdosproblems.com/363 (status DISPROVED (LEAN));
resolution: M. Ulas, On products of disjoint blocks of consecutive integers, Enseign. Math. (2)
(2005), 331-334; M. Bauer and M. A. Bennett, On a question of Erdős and Graham, Enseign. Math. (2)
(2007), 259-264, Ulas: infinitely many solutions for n = 4 and n ≥ 6 intervals of size 4; Bauer and
Bennett: n = 3, 5 (erdosproblems.com/363).
-/
public theorem_wanted finitelyManySquareIntervalProducts_refuted :
    ¬ finitelyManySquareIntervalProducts

end MathlibExt.NumberTheory.SquareProductDisjointIntervalsErdosProblem363Wanted
