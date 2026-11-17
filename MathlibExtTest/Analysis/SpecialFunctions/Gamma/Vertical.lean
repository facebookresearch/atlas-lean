/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.SpecialFunctions.Gamma.Vertical

/-!
# Tests for the Gamma function on vertical lines
-/

open Complex Filter Asymptotics

@[expose] public section

example : ‖Gamma 1‖ ≤ Real.Gamma (1 : ℂ).re := norm_Gamma_le_Gamma_re (by simp)

/-- The bound is sharp on the real axis. -/
example : ‖Gamma 1‖ = Real.Gamma (1 : ℂ).re := by simp

example : mellin (fun t : ℝ => ((Real.exp (-t) : ℝ) : ℂ)) 1 = 1 := by
  rw [mellin_exp_neg (by simp), Gamma_one]

example (t : ℝ) : ‖Gamma ((1 : ℝ) + t * I)‖ ≤ Real.Gamma (1 + 2) / ‖((1 : ℝ) : ℂ) + t * I‖ ^ 2 :=
  norm_Gamma_vertical_le one_pos t

/-- Mellin inversion at `σ = y = 1`. -/
example : (1 / (2 * Real.pi)) • ∫ t : ℝ, ((1 : ℝ) : ℂ) ^ (((1 : ℝ) : ℂ) + t * I) *
    Gamma (((1 : ℝ) : ℂ) + t * I) = ((Real.exp (-1) : ℝ) : ℂ) := by
  simpa using integral_cpow_mul_Gamma_vertical (σ := 1) (y := 1) one_pos one_pos

/-- Stirling at `σ = 1/2`: `|Γ(1/2 + it)| ∼ √(2π) e^{-π|t|/2}`. -/
example : IsEquivalent (comap (fun t : ℝ => |t|) atTop)
    (fun t : ℝ => ‖Gamma ((1 / 2 : ℝ) + t * I)‖)
    (fun t : ℝ => Real.exp (-(Real.pi * |t|) / 2) * Real.sqrt (2 * Real.pi)) := by
  simpa using norm_Gamma_vertical_isEquivalent (1 / 2)

example : ∃ R : ℝ, 1 ≤ R ∧ ∀ u : ℝ, R ≤ |u| →
    ‖Gamma ((1 : ℝ) + u * I)‖ ≤ 3 * |u| ^ ((1 : ℝ) - 2) * ‖Gamma ((2 : ℝ) + u * I)‖ :=
  exists_norm_Gamma_vertical_le_mul_rpow 1 2

example : ∃ M T : ℝ, 0 ≤ M ∧ ∀ t : ℝ, T ≤ |t| →
    ‖Gamma ((1 / 2 : ℝ) * (2 + t * I) + 0)‖ * ‖(Gamma ((1 / 2 : ℝ) * (-1 + t * I) + 0))⁻¹‖ ≤
      M * |t| ^ (3 * (1 / 2 : ℝ)) :=
  exists_norm_Gamma_line_two_mul_inv_line_neg_one_le (1 / 2) (by norm_num) 0
