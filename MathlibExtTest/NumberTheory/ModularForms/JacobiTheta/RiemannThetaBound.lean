/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ModularForms.JacobiTheta.RiemannThetaBound
import Mathlib.Algebra.Order.Star.Real

open Real Matrix Javanpeykar

/-! Concrete instances of the Gaussian-sum and theta-function bounds. -/

#check @tsum_exp_neg_pi_mul_add_sq_le
#check @tsum_exp_neg_sum_mul_add_sq
#check @summable_exp_neg_sum_mul_add_sq
#check @two_pow_mul_one_add_pow_le
#check @average_le_of_le_of_average_le
#check @riemannTheta
#check @summable_exp_neg_pi_quadForm
#check @summable_norm_riemannTheta_term
#check @exp_mul_norm_riemannTheta_le

/-- The one-variable bound at `t = 1`, `b = 1/2`. -/
example : ∑' n : ℤ, Real.exp (-π * 1 * (n + 1 / 2) ^ 2) ≤ 2 / (1 - Real.exp (-π * 1)) :=
  (tsum_exp_neg_pi_mul_add_sq_le one_pos (1 / 2)).1

/-- The same sum is at most `2(1 + 1/π)`. -/
example : ∑' n : ℤ, Real.exp (-π * 1 * (n + 1 / 2) ^ 2) ≤ 2 * (1 + 1 / (π * 1)) :=
  (tsum_exp_neg_pi_mul_add_sq_le one_pos (1 / 2)).1.trans
    (tsum_exp_neg_pi_mul_add_sq_le one_pos (1 / 2)).2

/-- The product formula for `g = 2`, `a = (1, 2)`, `b = (0, 1/3)`. -/
example : ∑' n : Fin 2 → ℤ,
      Real.exp (-∑ i, (![1, 2] : Fin 2 → ℝ) i * ((n i : ℝ) + (![0, 1 / 3] : Fin 2 → ℝ) i) ^ 2) =
    (∑' m : ℤ, Real.exp (-1 * (m + 0) ^ 2)) * ∑' m : ℤ, Real.exp (-2 * (m + 1 / 3) ^ 2) := by
  rw [tsum_exp_neg_sum_mul_add_sq, Fin.prod_univ_two]
  simp

/-- The product formula with a negative coefficient: both sides are `0`. -/
example : ∑' n : Fin 1 → ℤ,
      Real.exp (-∑ i, (![-1] : Fin 1 → ℝ) i * ((n i : ℝ) + (0 : Fin 1 → ℝ) i) ^ 2) =
    ∑' m : ℤ, Real.exp (-(-1) * (m + 0) ^ 2) := by
  rw [tsum_exp_neg_sum_mul_add_sq, Fin.prod_univ_one]
  simp

/-- Convergence of a two-variable Gaussian sum. -/
example : Summable fun n : Fin 2 → ℤ =>
    Real.exp (-∑ i, (![1, 2] : Fin 2 → ℝ) i * ((n i : ℝ) + (0 : Fin 2 → ℝ) i) ^ 2) :=
  summable_exp_neg_sum_mul_add_sq (fun i => by fin_cases i <;> norm_num) 0

/-- The numerical bound at `g = 1`: `2(1 + 2/(π√3)) ≤ 2⁸`. -/
example : (2 : ℝ) ^ 1 * (1 + 2 / (π * √3 *
    ((4 / ((1 : ℕ) : ℝ) ^ 3) ^ (1 - 1) * (3 / 4 : ℝ) ^ (1 * (1 - 1) / 2)))) ^ 1 ≤
    (2 : ℝ) ^ (3 * 1 ^ 3 + 5 * 1) :=
  two_pow_mul_one_add_pow_le 1

/-- The numerical bound at `g = 3`. -/
example : (2 : ℝ) ^ 3 * (1 + 2 / (π * √3 *
    ((4 / ((3 : ℕ) : ℝ) ^ 3) ^ (3 - 1) * (3 / 4 : ℝ) ^ (3 * (3 - 1) / 2)))) ^ 3 ≤
    (2 : ℝ) ^ (3 * 3 ^ 3 + 5 * 3) :=
  two_pow_mul_one_add_pow_le 3

/-- The averaging step for `g = 1`, `N = 2`, `h = 0`, `D = (0, 0)` and
`L = (8 log 2, 8 log 2 - 1)`. -/
example : 1 / ((2 : ℕ) : ℝ) * ∑ j, ![8 * Real.log 2, 8 * Real.log 2 - 1] j ≤
    ((1 : ℕ) : ℝ) / 4 * Real.log (max 1 0) +
      (4 * ((1 : ℕ) : ℝ) ^ 3 + 5 * ((1 : ℕ) : ℝ) + 1) * Real.log 2 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine average_le_of_le_of_average_le 1 2 0 _ ![0, 0] (fun j => ?_) ?_
  · fin_cases j <;> simp <;> linarith
  · simp
    nlinarith

/-- The theta series majorant for `g = 2`, `τ = i · 1`, `z = 0`, `b = 0`. -/
example : Real.exp (-π * ((fun i => ((0 : Fin 2 → ℂ) i).im) ⬝ᵥ
      ((Complex.I • (1 : Matrix (Fin 2) (Fin 2) ℂ)).map Complex.im)⁻¹ *ᵥ
        fun i => ((0 : Fin 2 → ℂ) i).im)) *
      ‖riemannTheta 0 (Complex.I • (1 : Matrix (Fin 2) (Fin 2) ℂ))‖ ≤
    ∑' n : Fin 2 → ℤ, Real.exp (-π * ((fun i => (n i : ℝ) + (0 : Fin 2 → ℝ) i) ⬝ᵥ
      ((Complex.I • (1 : Matrix (Fin 2) (Fin 2) ℂ)).map Complex.im) *ᵥ
        fun i => (n i : ℝ) + (0 : Fin 2 → ℝ) i)) := by
  have hY : (Complex.I • (1 : Matrix (Fin 2) (Fin 2) ℂ)).map Complex.im = 1 := by
    ext i j
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  refine exp_mul_norm_riemannTheta_le _ (hY ▸ PosDef.one) 0 0 ?_
  rw [hY, one_mulVec]
  ext i
  simp
