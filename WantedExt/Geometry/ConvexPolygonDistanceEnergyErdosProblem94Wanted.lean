/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Squared distance multiplicities of convex polygons (Erdős Problem 94)

Erdős Problem 94: suppose `n` points in `ℝ²` determine a convex polygon and the set of distances
between them is `{u_1, …, u_t}`. Suppose `u_i` appears as the distance between `f(u_i)` many pairs
of points. Then `∑_i f(u_i)² ≪ n³`.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Convex.Independent
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import MathlibExt.Geometry.Metric

@[expose] public section

namespace MathlibExt.Geometry.ConvexPolygonDistanceEnergyErdosProblem94Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #94, https://www.erdosproblems.com/94 (status PROVED
(LEAN)). UnsolvedMath record UM-30006719 (`EP-94`), dataset ulamai/UnsolvedMath v1.8.0.

Convex position as in Problem 93 (`ConvexIndependent ℝ`); the distances and their multiplicities are
MathlibExt's `distanceSet` and `distanceMultiplicity` (unordered pairs, so `∑ f(u_i) = C(n, 2)`); `≪
n³` is one constant `C` for all `n`. Compared with the formal-conjectures statement
`ErdosProblems/94.lean` (`erdos_94`, equivalent; no code imported).
-/

/-- Erdős Problem 94: for `n` points of the plane forming a convex polygon, with distances
`u_1, …, u_t` occurring `f(u_i)` times (unordered pairs; `distanceSet` and `distanceMultiplicity`,
MathlibExt), `∑ f(u_i)² ≪ n³`. -/
def convexPositionDistanceEnergy : Prop :=
  ∃ C : ℝ, ∀ A : Finset (EuclideanSpace ℝ (Fin 2)),
    ConvexIndependent ℝ (fun x : A => (x : EuclideanSpace ℝ (Fin 2))) →
      ∑ u ∈ distanceSet A, (distanceMultiplicity A u : ℝ) ^ 2 ≤ C * (A.card : ℝ) ^ 3

/--
Resolved true: Lefmann and Thiele proved `∑_i f(u_i)² ≪ n³` for every set of `n` points of the plane
with no three on a line, in particular for points in convex position; erdosproblems.com/94 lists the
problem as proved. Source: T. F. Bloom, Erdős Problems, Problem #94,
https://www.erdosproblems.com/94 (status PROVED (LEAN)); resolution: H. Lefmann and T. Thiele, Point
sets with distinct distances, Combinatorica (1995), 379-408, erdosproblems.com/94: Lefmann and
Thiele prove ∑ f(u_i)² ≪ n³ under the weaker assumption that no three points are on a line,
https://www.erdosproblems.com/94.
-/
public theorem_wanted convexPositionDistanceEnergy_holds : convexPositionDistanceEnergy

end MathlibExt.Geometry.ConvexPolygonDistanceEnergyErdosProblem94Wanted
