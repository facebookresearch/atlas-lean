/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Analysis.SineIntegral

/-! # Tests for `MathlibExt.Analysis.SineIntegral`

Boundary values (`Si 0 = 0`, `s = 0` in the change of variables, negative scale `s = -1` in the
limit), non-vacuity (`Si 1 > 0`, computed from the definition, so `Si` is not identically `0`),
and the moved Dirichlet-integral results used from their new location. -/

open MathlibExt.Analysis.SineIntegral Real Filter Topology

namespace MathlibExtTest.SineIntegral

/-- `Si 0 = 0`, straight from the definition. -/
example : sineIntegral 0 = 0 := by simp [sineIntegral]

example : sineIntegral 0 = 0 := sineIntegral_zero

/-- Non-vacuity: `Si 1 > 0`, since `sinc > 0` on `(0, 1]`. -/
example : 0 < sineIntegral 1 := by
  rw [sineIntegral]
  refine intervalIntegral.intervalIntegral_pos_of_pos_on
    (continuous_sinc.intervalIntegrable 0 1) (fun u hu => ?_) zero_lt_one
  rw [sinc_of_ne_zero hu.1.ne']
  exact div_pos (sin_pos_of_pos_of_lt_pi hu.1 (hu.2.trans (by linarith [two_le_pi]))) hu.1

/-- Oddness at `z = 1`. -/
example : sineIntegral (-1) = -sineIntegral 1 := sineIntegral_neg 1

/-- The Dirichlet integral. -/
example : Tendsto sineIntegral atTop (𝓝 (π / 2)) := tendsto_sineIntegral_atTop

/-- The rate at `T = 4`: `|Si 4 - π / 2| ≤ 1 / 2`. -/
example : |sineIntegral 4 - π / 2| ≤ 1 / 2 := by
  have h := abs_sineIntegral_sub_le (T := 4) (by norm_num)
  norm_num at h
  exact h

/-- Negative scale: `Si(-T) → -π / 2`. -/
example : Tendsto (fun T => sineIntegral (-1 * T)) atTop (𝓝 (-(π / 2))) := by
  have h := tendsto_sineIntegral_mul_atTop (-1)
  rwa [Real.sign_of_neg (by norm_num), mul_neg_one] at h

/-- Zero scale: `Si(0 · T) → 0 = (π / 2) sign 0`. -/
example : Tendsto (fun T => sineIntegral (0 * T)) atTop (𝓝 0) := by
  have h := tendsto_sineIntegral_mul_atTop 0
  rwa [Real.sign_zero, mul_zero] at h

example (z : ℝ) : |sineIntegral z| ≤ 4 := abs_sineIntegral_le z

example : Continuous sineIntegral := continuous_sineIntegral

/-- Boundary `s = 0` of the change of variables: both sides vanish. -/
example (T : ℝ) : ∫ t in (0 : ℝ)..T, (0 : ℝ) * sinc (t * 0) = sineIntegral (0 * T) :=
  integral_mul_sinc 0 T

example (T : ℝ) : sineIntegral (0 * T) = 0 := by simp [sineIntegral_zero]

/-- The Laplace representation at `T = π`, where `sin π = 0` and `cos π = -1`. -/
example : sineIntegral π = ∫ t in Set.Ioi 0, (1 + exp (-(π * t))) / (1 + t ^ 2) := by
  rw [sineIntegral_eq pi_pos]
  simp

end MathlibExtTest.SineIntegral
