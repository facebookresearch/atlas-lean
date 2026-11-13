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

Intervals consist of positive integers (an interval containing `0` has product `0`, a square).
Collections are lists of `Finset.Icc` intervals. `finitelyManySquareIntervalProducts` states the
claim for each fixed number `n` of intervals, with every size at least `4` and otherwise free.
`finitelyManySquareIntervalProductsOfSizes` also fixes the sizes `k₁, …, kₙ ≥ 4`, as in the
formal-conjectures statement `ErdosProblems/363.lean` (equivalent, with positivity of the intervals
built into the predicate; no code imported; without fixing the number of intervals and their sizes,
finiteness already fails by a result of Skałba). The fixed-count claim implies the fixed-size one,
since the collections of sizes `ks` have `ks.length` intervals of at least `4` elements each, so
refuting the fixed-size claim is the stronger result.
-/

/-- `S` is a list of pairwise disjoint intervals `[a, b]` of positive integers whose sizes are the
entries of `ks` and whose elements multiply to a perfect square. -/
def IsSquareIntervalCollection (ks : List ℕ) (S : List (Finset ℕ)) : Prop :=
  (∀ I ∈ S, ∃ a b : ℕ, 0 < a ∧ I = Finset.Icc a b) ∧ S.Pairwise Disjoint ∧
    S.map Finset.card = ks ∧ IsSquare (S.map fun I => ∏ m ∈ I, m).prod

/-- Erdős Problem 363: for every number `n` of intervals, only finitely many collections of `n`
pairwise disjoint intervals of positive integers, each with at least `4` elements, have a square
product. The sizes of the intervals are not fixed. -/
def finitelyManySquareIntervalProducts : Prop :=
  ∀ n : ℕ, {S : List (Finset ℕ) | S.length = n ∧ (∀ I ∈ S, 4 ≤ I.card) ∧
    IsSquareIntervalCollection (S.map Finset.card) S}.Finite

/-- Erdős Problem 363 with the sizes fixed as well, as in formal-conjectures: for all sizes
`k₁, …, kₙ ≥ 4`, only finitely many collections of disjoint intervals of positive integers of these
sizes have a square product. `finitelyManySquareIntervalProducts` implies it. -/
def finitelyManySquareIntervalProductsOfSizes : Prop :=
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
public theorem_wanted finitelyManySquareIntervalProductsOfSizes_refuted :
    ¬ finitelyManySquareIntervalProductsOfSizes

/--
Resolved false: Ulas's infinitely many collections of four disjoint blocks of four consecutive
positive integers with a square product all consist of four intervals of at least `4` elements. This
follows from `finitelyManySquareIntervalProductsOfSizes_refuted`, the stronger statement. Source:
T. F. Bloom, Erdős Problems, Problem #363, https://www.erdosproblems.com/363; resolution: M. Ulas,
On products of disjoint blocks of consecutive integers, Enseign. Math. (2) (2005), 331-334.
-/
public theorem_wanted finitelyManySquareIntervalProducts_refuted :
    ¬ finitelyManySquareIntervalProducts

end MathlibExt.NumberTheory.SquareProductDisjointIntervalsErdosProblem363Wanted
