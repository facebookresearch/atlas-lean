/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Calculus.WeightedSixthPowerGagliardoNirenberg
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

open MeasureTheory
open MathlibExt.Analysis.Calculus.WeightedSixthPowerGagliardoNirenbergWanted

-- The exponential weight attains the allowed logarithmic derivative bound of one.
example : ∃ C : ℝ, 0 < C ∧ ∀ u : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) u →
    HasCompactSupport u →
      (∫ x : ℝ, u x ^ 6 * Real.exp x) ≤ C * (eLpNorm u 2 volume).toReal ^ 4 *
        ∫ x : ℝ, (|deriv u x| ^ 2 + |u x| ^ 2) * Real.exp x := by
  obtain ⟨C, hC, h⟩ := exists_integral_pow_six_mul_weight_le
  have hlog : eLpNorm (fun x : ℝ ↦ deriv Real.exp x / Real.exp x) ⊤ volume ≤ 1 := by
    have heq : (fun x : ℝ ↦ deriv Real.exp x / Real.exp x) = fun _ ↦ (1 : ℝ) := by
      funext x
      rw [Real.deriv_exp, div_self (Real.exp_pos x).ne']
    rw [heq, eLpNorm_exponent_top aestronglyMeasurable_const]
    exact eLpNormEssSup_le_of_ae_eNorm_bound (.of_forall fun _ ↦ by simp)
  exact ⟨C, hC, h Real.exp Real.exp_pos Real.contDiff_exp hlog⟩
