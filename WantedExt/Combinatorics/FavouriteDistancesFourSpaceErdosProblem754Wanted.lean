/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Equidistant points in four-space (Erdős Problem 754)

Erdős Problem 754: let `f(n)` be maximal such that there exists a set `A` of `n` points in `ℝ⁴` in
which every `x ∈ A` has at least `f(n)` points in `A` equidistant from `x`. Is it true that `f(n) ≤
n / 2 + O(1)`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

namespace MathlibExt.Combinatorics.FavouriteDistancesFourSpaceErdosProblem754Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #754, https://www.erdosproblems.com/754 (status PROVED
(LEAN)). UnsolvedMath record UM-30007014 (`EP-754`), dataset ulamai/UnsolvedMath v1.8.0.

Points lie in `EuclideanSpace ℝ (Fin 4)`; "`f` points equidistant from `x`" is `f` points of `A` at
one distance `r(x) > 0` from `x`. The bound is stated for every nonempty `A` and every `f` attained,
so it bounds the maximum `f(n)` (for empty `A` every `f` would qualify vacuously).
-/

/-- Erdős Problem 754: `f(n) ≤ n / 2 + O(1)`, where `f(n)` is the largest `f` such that some set
`A` of `n ≥ 1` points of `ℝ⁴` has, for every `x ∈ A`, at least `f` points of `A` at one common
distance `r(x) > 0` from `x`. -/
def favouriteDistanceCountHalfPlusConstant : Prop :=
  ∃ C : ℝ, ∀ (A : Finset (EuclideanSpace ℝ (Fin 4))) (f : ℕ), A.Nonempty →
    (∀ x ∈ A, ∃ r : ℝ, 0 < r ∧ f ≤ {y | y ∈ A ∧ dist x y = r}.ncard) →
      (f : ℝ) ≤ A.card / 2 + C

/--
Resolved true: Swanepoel proved that for any finite `A ⊂ ℝ⁴` with `|A| = n` and any choice of
distances `r(x) > 0`, `∑_{x ∈ A} #{y ∈ A : |x - y| = r(x)} ≤ n²/2 + O(n)`, which gives `f(n) ≤ n / 2
+ O(1)`; erdosproblems.com/754 lists the problem as proved. Source: T. F. Bloom, Erdős Problems,
Problem #754, https://www.erdosproblems.com/754 (status PROVED (LEAN)); resolution: K. J. Swanepoel,
Favourite distances in high dimensions, Thirty Essays on Geometric Graph Theory (2013), 499-519,
abstract of arXiv:1108.4817: f_d(n) = max ∑_{x ∈ S} e_r(x, S) = (1 - 1/⌊d/2⌋) n² + Θ(n) for even d
(n²/2 + O(n) for d = 4); erdosproblems.com/754: proved by Swanepoel (Avis, Erdős and Pach had n/2 +
2 ≤ f(n) ≤ (1 + o(1)) n/2), https://arxiv.org/abs/1108.4817.
-/
public theorem_wanted favouriteDistanceCountHalfPlusConstant_holds :
    favouriteDistanceCountHalfPlusConstant

end MathlibExt.Combinatorics.FavouriteDistancesFourSpaceErdosProblem754Wanted
