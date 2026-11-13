/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Sums of squared distance multiplicities in the plane (Erdős Problem 95)

Erdős Problem 95: let `x_1, …, x_n ∈ ℝ²` determine the set of distances `{u_1, …, u_t}`. Suppose
`u_i` appears as the distance between `f(u_i)` many pairs of points. Then for all `ε > 0`, `∑_i
f(u_i)² ≪_ε n^{3 + ε}`.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import MathlibExt.Geometry.Metric

@[expose] public section

namespace MathlibExt.Geometry.DistanceMultiplicityEnergyErdosProblem95Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #95, https://www.erdosproblems.com/95 (status PROVED
(LEAN)). UnsolvedMath record UM-30006720 (`EP-95`), dataset ulamai/UnsolvedMath v1.8.0.

Finite sets of `n` distinct points of `EuclideanSpace ℝ (Fin 2)`; distances and multiplicities are
MathlibExt's `distanceSet` and `distanceMultiplicity` (unordered pairs), and `≪_ε` is a constant
depending only on `ε`. Compared with the formal-conjectures statement `ErdosProblems/95.lean`
(`erdos_95`, equivalent; no code imported).
-/

/-- Erdős Problem 95: for every `ε > 0` there is `C` such that for every set of `n` points of the
plane, with distances `u_1, …, u_t` occurring `f(u_i)` times (unordered pairs; `distanceSet` and
`distanceMultiplicity`, MathlibExt), `∑ f(u_i)² ≤ C n^{3 + ε}`. -/
def distanceEnergyBound : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ A : Finset (EuclideanSpace ℝ (Fin 2)),
    ∑ u ∈ distanceSet A, (distanceMultiplicity A u : ℝ) ^ 2 ≤ C * (A.card : ℝ) ^ (3 + ε)

/--
Resolved true: Guth and Katz proved (Proposition 2.2, counting quadruples `(p₁, p₂, p₃, p₄)` with
`|p₁ - p₂| = |p₃ - p₄| ≠ 0`) that `∑_i f(u_i)² ≪ n³ log n`, which is `≪_ε n^{3 + ε}`;
erdosproblems.com/95 lists the problem as proved. Source: T. F. Bloom, Erdős Problems, Problem #95,
https://www.erdosproblems.com/95 (status PROVED (LEAN)); resolution: L. Guth and N. H. Katz, On the
Erdős distinct distances problem in the plane, Ann. of Math. (2) (2015), 155-190, arXiv:1011.4105,
Proposition 2.2: the number of quadruples (p₁, p₂, p₃, p₄) of points with d(p₁, p₂) = d(p₃, p₄) ≠ 0
is ≲ N³ log N; erdosproblems.com/95: Guth and Katz proved ∑ f(u_i)² ≪ n³ log n,
https://arxiv.org/abs/1011.4105.
-/
public theorem_wanted distanceEnergyBound_holds : distanceEnergyBound

end MathlibExt.Geometry.DistanceMultiplicityEnergyErdosProblem95Wanted
