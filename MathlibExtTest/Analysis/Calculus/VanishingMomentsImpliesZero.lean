/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Calculus.VanishingMomentsImpliesZero

/-! # Tests for vanishing moments on the unit interval -/

open Set MathlibExt.Analysis.Calculus.VanishingMomentsImpliesZeroWanted

-- Equal moments determine two continuous functions at every point of the closed interval.
example {f g : ℝ → ℝ} (hf : ContinuousOn f (Icc 0 1)) (hg : ContinuousOn g (Icc 0 1))
    (h : ∀ n : ℕ, (∫ x in 0..1, f x * x ^ n) = ∫ x in 0..1, g x * x ^ n) :
    EqOn f g (Icc 0 1) := by
  have hzero := eqOn_zero_of_integral_mul_pow_eq_zero (f - g) (hf.sub hg) fun n => by
    simp only [Pi.sub_apply, sub_mul]
    rw [intervalIntegral.integral_sub, h n, sub_self]
    · exact (hf.mul (continuous_pow n).continuousOn).intervalIntegrable_of_Icc zero_le_one
    · exact (hg.mul (continuous_pow n).continuousOn).intervalIntegrable_of_Icc zero_le_one
  exact fun x hx => sub_eq_zero.mp (hzero hx)

-- A spike at the left endpoint has every moment zero, so continuity there is essential.
example : ¬ ContinuousOn (fun x : ℝ => if x = 0 then (1 : ℝ) else 0) (Icc 0 1) := by
  intro hf
  have hzero := eqOn_zero_of_integral_mul_pow_eq_zero _ hf fun n => by
    calc
      _ = ∫ _ in (0 : ℝ)..1, (0 : ℝ) := by
        apply intervalIntegral.integral_congr_Ioo_of_le zero_le_one
        intro x hx
        simp [hx.1.ne']
      _ = 0 := by simp
  simpa using hzero (left_mem_Icc.mpr zero_le_one)
