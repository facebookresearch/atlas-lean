/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.ScalarCalculus
import MathlibExt.NumberTheory.AlternatingReciprocalIntegral

-- At the lower bounds r = m = 2 and α = 0, the integrand simplifies away from x = 1.
example : ∑' i : ℕ, (1 / (2 + (i : ℝ) * 2) - 1 / (3 + (i : ℝ) * 2)) = 1 - Real.log 2 := by
  have h := MetaMathlibExt.tsum_alternating_inv_eq_integral 2 2 le_rfl le_rfl 0 le_rfl zero_lt_one
  norm_num at h
  simp only [one_div]
  rw [h]
  have hint : IntervalIntegrable (fun x : ℝ => 1 / (1 + x)) MeasureTheory.volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    refine continuousOn_const.div (continuous_const.add continuous_id).continuousOn fun x hx => ?_
    rw [Set.uIcc_of_le zero_le_one] at hx
    linarith [hx.1]
  calc
    _ = ∫ x in (0 : ℝ)..1, 1 - 1 / (1 + x) := by
      apply intervalIntegral.integral_congr_Ioo_of_le zero_le_one
      intro x hx
      have hx₀ := hx.1
      have hx₁ := hx.2
      have hden : 1 - x ^ 2 ≠ 0 :=
        sub_ne_zero.mpr (pow_lt_one₀ hx₀.le hx₁ two_ne_zero).ne'
      dsimp only
      field_simp [hden, show 1 + x ≠ 0 by linarith]
      ring
    _ = _ := by
      rw [intervalIntegral.integral_sub intervalIntegrable_const hint,
        intervalIntegral.integral_const, (ScalarCalculus.integral_rationalRates 1).2 (by norm_num)]
      norm_num
