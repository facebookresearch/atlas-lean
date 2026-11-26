/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum
import MathlibExt.NumberTheory.LSeries.RiemannZetaLogDeriv

/-! # Tests for the bound on the logarithmic derivative of zeta -/

open MetaMathlibExt

-- The same witnesses work on both horizontal edges and on the real axis.
example : ∃ C α₀ : ℝ, 0 < α₀ ∧ ∀ α : ℝ, 0 < α → α < α₀ →
    ∀ τ ∈ ({-(1 / 2), 0, 1 / 2} : Set ℝ),
      ‖deriv riemannZeta (1 + α + τ * Complex.I) / riemannZeta (1 + α + τ * Complex.I)‖ ≤
        1 / ‖(α : ℂ) + τ * Complex.I‖ + C := by
  obtain ⟨C, α₀, hα₀, h⟩ := exists_norm_logDeriv_riemannZeta_le_inv_norm_add
  refine ⟨C, α₀, hα₀, fun α hα hlt τ hτ ↦ h α τ hα hlt ?_⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hτ
  rcases hτ with rfl | rfl | rfl <;> norm_num
