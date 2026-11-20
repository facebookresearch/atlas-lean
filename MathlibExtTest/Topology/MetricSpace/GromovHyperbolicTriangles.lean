/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.MetricSpace.GromovHyperbolicTriangles

@[expose] public section

namespace MathlibExtTest.GromovHyperbolicTriangles

open Metric

/-- Geodesic triangles in `ℝ` are `0`-thin. -/
example : TrianglesThin ℝ 0 := by
  simpa using isDeltaHyperbolic_real.trianglesThin

/-- The thin-triangle criterion recovers `0`-hyperbolicity of `ℝ` (a geodesic space). -/
example : IsDeltaHyperbolic ℝ 0 :=
  isDeltaHyperbolic_of_trianglesThin le_rfl (isGeodesicSpace_of_normedSpace ℝ)
    (by simpa using isDeltaHyperbolic_real.trianglesThin)

/-- Base-point change on `ℝ` with base point `0`. -/
example : IsDeltaHyperbolic ℝ (2 * 0) :=
  isDeltaHyperbolic_two_mul_of_basepoint (o := (0 : ℝ)) le_rfl
    (fun x y z => isDeltaHyperbolic_real.four_point 0 x y z)

/-- A bounded space: the unit interval is `1`-hyperbolic. -/
example : IsDeltaHyperbolic (Set.Icc (0 : ℝ) 1) 1 :=
  isDeltaHyperbolic_of_forall_dist_le zero_le_one fun x y => by
    rw [Subtype.dist_eq, Real.dist_eq, abs_le]
    constructor <;> linarith [x.2.1, x.2.2, y.2.1, y.2.2]

example : IsDeltaHyperbolic ℤ 0 := isDeltaHyperbolic_int

end MathlibExtTest.GromovHyperbolicTriangles
