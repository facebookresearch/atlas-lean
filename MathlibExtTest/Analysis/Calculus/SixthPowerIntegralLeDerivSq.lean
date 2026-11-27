/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Calculus.SixthPowerIntegralLeDerivSq
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-! # The sixth-power bound on rescaled smooth bump functions -/

open MathlibExt.Analysis.Calculus.SixthPowerIntegralLeDerivSqWanted
open MeasureTheory

-- One constant works for bumps of every center and radius after normalizing their square integral.
example : ∃ C : ℝ, 0 < C ∧ ∀ (c : ℝ) (b : ContDiffBump c),
    let u := fun t ↦ b t / √(∫ x, b x ^ 2)
    (∫ t, u t ^ 2) = 1 ∧ (∫ t, u t ^ 6) ≤ C * ∫ t, deriv u t ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := exists_integral_pow_six_le_integral_deriv_sq_of_integral_sq_eq_one
  refine ⟨C, hC, fun c b ↦ ?_⟩
  let m := ∫ x, b x ^ 2
  have hb : b c = 1 := b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)
  have hm : 0 < m := (b.continuous.pow 2).integral_pos_of_hasCompactSupport_nonneg_nonzero
    (b.hasCompactSupport.comp_left (g := fun z ↦ z ^ 2) (by norm_num))
    (fun _ ↦ sq_nonneg _) (x := c) (by simp [hb])
  have hnorm : (∫ x, (b x / √m) ^ 2) = 1 := by
    simp_rw [div_pow, Real.sq_sqrt hm.le, integral_div]
    exact div_self hm.ne'
  exact ⟨hnorm, hbound _ (b.contDiff.div_const _) (b.hasCompactSupport.comp_left
    (g := fun z ↦ z / √m) (zero_div _)) hnorm⟩
