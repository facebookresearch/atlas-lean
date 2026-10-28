/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.SpecialFunctions.Gamma.Binet

/-!
# Tests for Binet's and Stirling's formulas

`1 / Γ` is a natural example of `Complex.HasGrowthOrder` with order `1`; the Weierstrass product
is checked at a pole and at `z = 1`, and the Binet and Stirling statements are instantiated.
-/

@[expose] public section

open Complex

/-- **Non-vacuity of `HasGrowthOrder`.** `1 / Γ` has order exactly `1`. -/
example : HasGrowthOrder (fun z => (Complex.Gamma z)⁻¹) 1 := hasGrowthOrder_inv_Gamma

/-- Its order is not `2`. -/
example : ¬ HasGrowthOrder (fun z => (Complex.Gamma z)⁻¹) 2 := fun h => by
  have := h.unique hasGrowthOrder_inv_Gamma
  norm_num at this

/-- `1 / Γ` is not of order at most `1 / 2`. -/
example : ¬ HasGrowthOrderLE (fun z => (Complex.Gamma z)⁻¹) (1 / 2) :=
  hasGrowthOrder_inv_Gamma.2 _ (by norm_num)

/-- The Weierstrass product at the pole `z = 0`: both sides are `0` (Mathlib's `Γ 0 = 0`). -/
example : (Complex.Gamma 0)⁻¹ = 0 := by
  rw [inv_Gamma_eq_exp_mul_tprod]
  simp

/-- The Weierstrass product at `z = 1` evaluates to `1`. -/
example : Complex.exp (Real.eulerMascheroniConstant * 1) * 1 *
    ∏' n : ℕ, (1 + 1 / ((n : ℂ) + 1)) * Complex.exp (-(1 / ((n : ℂ) + 1))) = 1 := by
  rw [← inv_Gamma_eq_exp_mul_tprod, Complex.Gamma_one, inv_one]

/-- The sawtooth bound at a half-integer and an integer. -/
example : ‖((((⌊(1 / 2 : ℝ)⌋ : ℝ) - 1 / 2 + 1 / 2 : ℝ) : ℂ))‖ ≤ 1 / 2 := norm_sawtooth_le _

example : IntervalIntegrable (fun u : ℝ => ((((⌊u⌋ : ℝ) - u + 1 / 2 : ℝ) : ℂ) / ((u : ℂ) + 1)))
    MeasureTheory.volume 0 5 :=
  intervalIntegrable_sawtooth_div_ofReal_add (fun u hu h => by
    have := congrArg Complex.re h
    simp at this
    linarith) le_rfl (by norm_num)

/-- **Binet at `z = 1`.** -/
example : ∃ I : ℂ, Filter.Tendsto (fun N : ℝ => ∫ u in (0 : ℝ)..N,
    ((((⌊u⌋ : ℝ) - u + 1 / 2 : ℝ) : ℂ) / ((u : ℂ) + 1))) Filter.atTop (nhds I) ∧
    1 = Complex.exp ((1 - 1 / 2) * Complex.log 1 - 1 + 1 / 2 * Complex.log (2 * Real.pi) + I) := by
  simpa using Gamma_eq_exp_binet 1 (by simp [Complex.slitPlane])

/-- **Stirling at `z = 1`** (sector `|arg z| ≤ π / 2`). -/
example : ∃ C : ℝ, ∃ E : ℂ, ‖E‖ ≤ C / ‖(1 : ℂ)‖ ∧ Complex.Gamma 1 =
    Complex.exp ((1 - 1 / 2) * Complex.log 1 - 1 + 1 / 2 * Complex.log (2 * Real.pi) + E) := by
  obtain ⟨C, hC⟩ := Gamma_eq_exp_stirling_sector (Real.pi / 2) (by positivity)
  exact ⟨C, hC 1 one_ne_zero (by simp; positivity) (by simp; positivity)⟩

/-- Stirling on the negative imaginary axis, `z = -i y`, is covered (`arg z = -π / 2`). -/
example (y : ℝ) (hy : 0 < y) : ∃ C : ℝ, ∃ E : ℂ, ‖E‖ ≤ C / ‖-(y : ℂ) * I‖ ∧
    Complex.Gamma (-(y : ℂ) * I) = Complex.exp ((-(y : ℂ) * I - 1 / 2) *
      Complex.log (-(y : ℂ) * I) - -(y : ℂ) * I + 1 / 2 * Complex.log (2 * Real.pi) + E) := by
  obtain ⟨C, hC⟩ := Gamma_eq_exp_stirling_sector (Real.pi / 2) (by positivity)
  have harg : Complex.arg (-(y : ℂ) * I) = -(Real.pi / 2) := by
    rw [show -(y : ℂ) * I = (y : ℂ) * (-I) by ring, Complex.arg_real_mul _ hy, Complex.arg_neg_I]
  refine ⟨C, hC _ (by simp [hy.ne']) (by rw [harg]; linarith) (by rw [harg]; linarith [Real.pi_pos])⟩
