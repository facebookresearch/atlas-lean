/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Calculus.SupNormEpsDerivPlusIntegral
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Tests for the sup norm bound on the unit interval -/

open Set MathlibExt.Analysis.Calculus.SupNormEpsDerivPlusIntegralWanted

-- The same constant must work for the constant 1 and for absolute value, whose
-- two-sided derivative vanishes by convention at 0 and equals 1 on (0, 1].
example {ε : ℝ} (hε : 0 < ε) : ∃ C ≥ (1 : ℝ), 1 ≤ ε + C / 2 := by
  obtain ⟨C, _, hC⟩ := exists_const_sSup_norm_le_mul_sSup_norm_deriv_add_mul_integral ε hε
  refine ⟨C, ?_, ?_⟩
  · simpa [(nonempty_Icc.mpr (zero_le_one : (0 : ℝ) ≤ 1)).image_const]
      using hC (fun _ => 1) contDiffOn_const
  have habs : ContDiffOn ℝ 1 (abs : ℝ → ℝ) (Icc 0 1) :=
    contDiffOn_id.congr fun x hx => abs_of_nonneg hx.1
  have hnorm : EqOn (fun x : ℝ => ‖|x|‖) id (Icc 0 1) := fun x hx => by
    simp [Real.norm_eq_abs, abs_of_nonneg hx.1]
  have hderiv : IsGreatest ((fun x : ℝ => ‖deriv (|·|) x‖) '' Icc 0 1) 1 := by
    refine ⟨⟨1, right_mem_Icc.mpr zero_le_one, by simp [deriv_abs_pos one_pos]⟩, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    rcases hx.1.eq_or_lt with h | h
    · subst x
      simp [deriv_abs_zero]
    · simp [deriv_abs_pos h]
  have hint : (∫ x in (0 : ℝ)..1, ‖|x|‖) = 1 / 2 := by
    rw [intervalIntegral.integral_congr (g := id) (by rwa [uIcc_of_le zero_le_one])]
    norm_num [id_def, integral_id]
  have h := hC abs habs
  rw [image_congr hnorm, image_id, hderiv.csSup_eq, hint] at h
  simpa [div_eq_mul_inv] using h
