/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Distributions.GaussianTail

/-!
# Tests for the standard-normal upper-tail bound

The half-line mass `gaussianReal_Ioi_zero` at a variance other than `1`, and the upper-tail bound
`gaussianReal_Ioi_le_half_exp` at `u = 0`, where it equals the half-line mass, at `u = 1`, and at
`u = 2`, where it is below `1 / 10`.
-/

open MeasureTheory ProbabilityTheory

namespace MathlibExtTest.Probability.Distributions.GaussianTail

/-- A centered Gaussian law of variance `4` gives mass `1 / 2` to `(0, ∞)`. -/
example : gaussianReal 0 4 (Set.Ioi 0) = 1 / 2 := gaussianReal_Ioi_zero (by norm_num)

/-- At `u = 0` the bound is `1 / 2`, the half-line mass, so it is attained. -/
example : gaussianReal 0 1 (Set.Ioi 0) ≤ ENNReal.ofReal (1 / 2 : ℝ) := by
  have h := gaussianReal_Ioi_le_half_exp (u := (0 : ℝ)) le_rfl
  rw [show (-(0 : ℝ) ^ 2 / 2) = 0 by norm_num, Real.exp_zero] at h
  exact h

/-- The bound at `u = 1`. -/
example : gaussianReal 0 1 (Set.Ioi 1) ≤ ENNReal.ofReal (Real.exp (-(1 : ℝ) ^ 2 / 2) / 2) :=
  gaussianReal_Ioi_le_half_exp (by norm_num)

/-- At `u = 2` the bound is `Real.exp (-2) / 2 ≤ 1 / 10`, since `Real.exp 2 ≥ 1 + 2 + 2 ^ 2 / 2`.
Without the factor `1 / 2`, or with exponent `-u ^ 2 / 4`, the bound would exceed `1 / 10`. -/
example : gaussianReal 0 1 (Set.Ioi 2) ≤ ENNReal.ofReal (1 / 10 : ℝ) := by
  refine (gaussianReal_Ioi_le_half_exp (by norm_num)).trans (ENNReal.ofReal_le_ofReal ?_)
  have h5 : (5 : ℝ) ≤ Real.exp 2 := by
    have h := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)
    norm_num at h
    linarith
  rw [show (-(2 : ℝ) ^ 2 / 2) = -2 by norm_num, Real.exp_neg]
  calc (Real.exp 2)⁻¹ / 2 ≤ (5 : ℝ)⁻¹ / 2 := by
        gcongr
    _ = 1 / 10 := by norm_num

end MathlibExtTest.Probability.Distributions.GaussianTail
