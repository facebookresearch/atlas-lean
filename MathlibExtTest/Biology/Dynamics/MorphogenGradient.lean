/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.Dynamics.MorphogenGradient

/-! Tests for the steady-state morphogen gradient: concrete values, the exponential profile as
the non-vacuity witness of `IsSteadyState`, junk values, and the French-flag boundary shift. -/

open Real

namespace MathlibExtTest.Biology.Dynamics.MorphogenGradient

open MathlibExt.Biology.Dynamics.MorphogenGradient

example : decayLength 4 1 = 2 := by
  rw [decayLength, show (4 : ℝ) / 1 = 2 ^ 2 by norm_num, sqrt_sq (by norm_num)]

/-- Source amplitude for unit parameters: `c(0) = 1`. -/
example : profile 1 1 1 0 = 1 := by simp [profile]

/-- Junk value outside the domain `k > 0`: `√(D / 0) = 0`. -/
example (D : ℝ) : decayLength D 0 = 0 := by simp [decayLength]

/-- **Non-vacuity witness.** The exponential profile is a bounded steady state. -/
example : IsSteadyState 1 1 1 (profile 1 1 1) (fun x ↦ -profile 1 1 1 x / decayLength 1 1) :=
  isSteadyState_profile one_pos one_pos

example (x : ℝ) (hx : 0 ≤ x) : profile 1 1 1 x = exp (-x) := by
  rw [eq_profile_of_isSteadyState one_pos one_pos (isSteadyState_profile one_pos one_pos) hx]
  simp [profile, decayLength]

/-- Unit parameters, threshold `1/2`: the boundary sits at `log 2`. -/
example : thresholdPosition 1 1 1 (1 / 2) = log 2 := by
  simp [thresholdPosition, decayLength]

example : profile 1 1 1 (log 2) = 1 / 2 :=
  (profile_eq_iff one_pos one_pos one_pos (by norm_num) _).2 (by
    simp [thresholdPosition, decayLength])

example (x : ℝ) : 1 / 2 ≤ profile 1 1 1 x ↔ x ≤ thresholdPosition 1 1 1 (1 / 2) :=
  le_profile_iff one_pos one_pos one_pos (by norm_num) x

/-- Doubling the source moves the threshold-`1/2` boundary from `log 2` to `2 log 2`. -/
example : thresholdPosition 1 1 2 (1 / 2) = 2 * log 2 := by
  have h := thresholdPosition_two_mul (D := 1) (k := 1) (j := 1) (θ := 1 / 2) one_pos one_pos
    one_pos (by norm_num)
  rw [mul_one] at h
  rw [h]; simp [thresholdPosition, decayLength]; ring

end MathlibExtTest.Biology.Dynamics.MorphogenGradient
