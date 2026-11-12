/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Geometry.LatitudeLongitudeSphere

open scoped BigOperators

/-- Concrete non-vacuous case: latitude `0`, longitude `0`, radius `5`
gives the point `(5, 0, 0)` with squared radius `25`. -/
example : ∑ i, (![5 * Real.cos 0 * Real.cos 0, 5 * Real.cos 0 * Real.sin 0,
      5 * Real.sin 0] i : ℝ) ^ 2 = 25 := by
  have h := EarthScience.lat_lon_on_sphere 5 0 0
  norm_num at h ⊢
  exact h

/-- Boundary case: the north pole, latitude `π / 2`, gives `(0, 0, R)`;
squared radius `R ^ 2` for `R = 3`. -/
example : ∑ i, (![3 * Real.cos (Real.pi / 2) * Real.cos 0,
      3 * Real.cos (Real.pi / 2) * Real.sin 0,
      3 * Real.sin (Real.pi / 2)] i : ℝ) ^ 2 = 9 := by
  have h := EarthScience.lat_lon_on_sphere 3 (Real.pi / 2) 0
  rw [Real.sin_pi_div_two, Real.cos_pi_div_two] at h
  norm_num at h ⊢
  exact h

/-- Boundary case: radius `R = 0` collapses the point to the origin with
squared radius `0`. -/
example : ∑ i, (![0 * Real.cos 1 * Real.cos 2, 0 * Real.cos 1 * Real.sin 2,
      0 * Real.sin 1] i : ℝ) ^ 2 = 0 := by
  have h := EarthScience.lat_lon_on_sphere 0 1 2
  norm_num at h ⊢
  exact h
