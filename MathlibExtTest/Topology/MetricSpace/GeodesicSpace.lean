/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.MetricSpace.GeodesicSpace

@[expose] public section

namespace MathlibExtTest.GeodesicSpace

open Metric

example : IsGeodesicSpace ℝ := isGeodesicSpace_of_normedSpace ℝ

example : IsGeodesicSpace (ℝ × ℝ) := isGeodesicSpace_of_normedSpace (ℝ × ℝ)

/-- In `ℝ`, a point at distance `1` from `0` and `2` from `3` exists. -/
example : ∃ z : ℝ, dist 0 z = 1 ∧ dist z 3 = dist (0 : ℝ) 3 - 1 :=
  (isGeodesicSpace_of_normedSpace ℝ).exists_dist_eq_dist_eq 0 3 zero_le_one
    (by rw [Real.dist_eq]; norm_num)

end MathlibExtTest.GeodesicSpace
