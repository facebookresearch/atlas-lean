/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The product of the multiplicities of the extreme distances (Erdős Problem 957)

Erdős Problem 957: let `A ⊂ ℝ²` be a set of size `n` and let `{d_1 < ⋯ < d_k}` be the set of
distinct distances determined by `A`. Let `f(d)` be the number of times the distance `d` is
determined. Is it true that `f(d_1) f(d_k) ≤ (9/8 + o(1)) n²`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import MathlibExt.Geometry.Metric

@[expose] public section

namespace MathlibExt.Geometry.ExtremeDistancesProductErdosProblem957Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #957, https://www.erdosproblems.com/957 (status
PROVED). UnsolvedMath record UM-30007099 (`EP-957`), dataset ulamai/UnsolvedMath v1.8.0.

`f(d)` counts unordered pairs (MathlibExt's `distanceMultiplicity`); `d_1` and `d_k` are the minimum
and maximum of `distanceSet A`, which is nonempty when `n ≥ 2`. `o(1)` is quantified as: for every
`ε > 0` and all large `n`. The follow-up remarks on `f(d_1) + f(d_k)` are commentary and not stated.
formal-conjectures has no statement of this problem.
-/

/-- Erdős Problem 957: `f(d₁) f(d_k) ≤ (9/8 + o(1)) n²` for `n`-point sets `A` of the plane, where
`d₁` and `d_k` are the smallest and the largest distance determined by `A` and `f(d)` counts the
unordered pairs at distance `d` (`distanceSet`, `distanceMultiplicity`, MathlibExt): for every
`ε > 0` and all large `n`, every such `A` with `|A| = n` has `f(d₁) f(d_k) ≤ (9/8 + ε) n²`. -/
def extremeDistanceMultiplicityProduct : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in Filter.atTop, ∀ A : Finset (EuclideanSpace ℝ (Fin 2)),
    A.card = n → ∀ h : (distanceSet A).Nonempty,
      (distanceMultiplicity A ((distanceSet A).min' h) : ℝ) *
          distanceMultiplicity A ((distanceSet A).max' h) ≤ (9 / 8 + ε) * (n : ℝ) ^ 2

/--
Resolved true: Dumitrescu proved (Theorem 1) that the multiplicities of the minimum and the maximum
distance of `n` points of the plane satisfy `f(d_1) f(d_k) ≤ (9/8) n² + O(n)`; erdosproblems.com/957
lists the problem as proved. Source: T. F. Bloom, Erdős Problems, Problem #957,
https://www.erdosproblems.com/957 (status PROVED); resolution: A. Dumitrescu, A product inequality
for extreme distances, Comput. Geom. (2019), 101577; conference version in SoCG 2019, LIPIcs 129,
Paper 30, Theorem 1: for n distinct points in the plane the multiplicities s_min and s_max of the
minimum and maximum distance satisfy s_min · s_max ≤ (9/8) n² + O(n),
https://drops.dagstuhl.de/storage/00lipics/lipics-vol129-socg2019/LIPIcs.SoCG.2019.30/LIPIcs.SoCG.2019.30.pdf.
-/
public theorem_wanted extremeDistanceMultiplicityProduct_holds : extremeDistanceMultiplicityProduct

end MathlibExt.Geometry.ExtremeDistancesProductErdosProblem957Wanted
