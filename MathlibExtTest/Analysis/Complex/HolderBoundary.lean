/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.Calculus.FDeriv.Basic
import MathlibExt.Analysis.Complex.HolderBoundary

set_option autoImplicit false

open scoped NNReal

-- `F = id` has `‖F′‖ = 1 = (1 - ‖z‖)^0`, so `α = 1` applies: `circleMap 0 1` is Lipschitz.
example : ∃ C' : ℝ≥0, HolderWith C' 1 fun t : ℝ => circleMap (0 : ℂ) 1 t :=
  Complex.holderWith_circleMap_of_norm_fderiv_le (F := id) (C := 1) one_pos one_pos le_rfl
    continuousOn_id differentiableOn_id fun z _ => by
      simp only [fderiv_id, NNReal.coe_one, sub_self, Real.rpow_zero, mul_one]
      exact ContinuousLinearMap.norm_id_le

-- The textbook's form `|F(e^{it₁}) - F(e^{it₂})| ≤ C' |t₁ - t₂|^α`.
example {F : ℂ → ℂ} {C : ℝ} {α : ℝ≥0} (hC : 0 < C) (hα_pos : 0 < α) (hα_le : α ≤ 1)
    (hcont : ContinuousOn F (Metric.closedBall 0 1))
    (hdiff : DifferentiableOn ℝ F (Metric.ball 0 1))
    (hgrad : ∀ z : ℂ, ‖z‖ < 1 → ‖fderiv ℝ F z‖ ≤ C * (1 - ‖z‖) ^ ((α : ℝ) - 1)) :
    ∃ C' : ℝ, ∀ t₁ t₂ : ℝ,
      ‖F (circleMap 0 1 t₁) - F (circleMap 0 1 t₂)‖ ≤ C' * |t₁ - t₂| ^ (α : ℝ) := by
  obtain ⟨C', h⟩ :=
    Complex.holderWith_circleMap_of_norm_fderiv_le hC hα_pos hα_le hcont hdiff hgrad
  exact ⟨C', fun t₁ t₂ => by simpa [dist_eq_norm, Real.dist_eq] using h.dist_le t₁ t₂⟩

#print axioms Complex.holderWith_circleMap_of_norm_fderiv_le
