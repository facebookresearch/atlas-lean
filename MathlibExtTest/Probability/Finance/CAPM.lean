/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Finance.CAPM
import Mathlib.Algebra.Order.Star.Real
import Mathlib.LinearAlgebra.Matrix.Notation

/-! # Tests for `MathlibExt.Probability.Finance.CAPM` -/

open Matrix MathlibExt.Probability.Finance.TangencyPortfolio MathlibExt.Probability.Finance.CAPM

namespace MathlibExtTest.CAPM

example : beta (1 : Matrix (Fin 2) (Fin 2) ℝ) ![1/4, 3/4] 1 = 6 / 5 := by
  have h1 : (![1/4, 3/4] : Fin 2 → ℝ) 1 = 3 / 4 := by simp
  have hden : (![1/4, 3/4] : Fin 2 → ℝ) ⬝ᵥ ![1/4, 3/4] = 10 / 16 := by
    show (∑ k, (![1/4, 3/4] : Fin 2 → ℝ) k * (![1/4, 3/4] : Fin 2 → ℝ) k) = 10 / 16
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    norm_num
  unfold beta
  rw [one_mulVec, h1, hden]
  norm_num

example : ((![1, 3] : Fin 2 → ℝ) 1 - 0)
    = beta 1 ![1/4, 3/4] 1 * ((![1, 3] : Fin 2 → ℝ) ⬝ᵥ ![1/4, 3/4] - 0) := by
  have hS : (1 : Matrix (Fin 2) (Fin 2) ℝ).PosDef := Matrix.PosDef.one
  have hwM : ∑ i, (![1/4, 3/4] : Fin 2 → ℝ) i = 1 := by
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    norm_num
  have hmuvM : (![1, 3] : Fin 2 → ℝ) ⬝ᵥ ![1/4, 3/4] = 5 / 2 := by
    show (∑ k, (![1, 3] : Fin 2 → ℝ) k * (![1/4, 3/4] : Fin 2 → ℝ) k) = 5 / 2
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    norm_num
  have hprem : (0 : ℝ) < (![1, 3] : Fin 2 → ℝ) ⬝ᵥ ![1/4, 3/4] - 0 := by
    rw [hmuvM]
    norm_num
  have hwMvM : (![1/4, 3/4] : Fin 2 → ℝ) ⬝ᵥ ![1/4, 3/4] = 10 / 16 := by
    show (∑ k, (![1/4, 3/4] : Fin 2 → ℝ) k * (![1/4, 3/4] : Fin 2 → ℝ) k) = 10 / 16
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    norm_num
  have heff : ∀ w : Fin 2 → ℝ, ∑ i, w i = 1 →
      sharpeRatio (1 : Matrix (Fin 2) (Fin 2) ℝ) ![1, 3] 0 w
        ≤ sharpeRatio (1 : Matrix (Fin 2) (Fin 2) ℝ) ![1, 3] 0 ![1/4, 3/4] := by
    intro w hw
    have hwne : w ≠ 0 := by
      intro hcon
      have h0 : ∑ i, w i = 0 := by simp [hcon]
      rw [hw] at h0
      exact one_ne_zero h0
    have hww : (0 : ℝ) < w ⬝ᵥ w := by
      have h := hS.dotProduct_mulVec_pos hwne
      rwa [star_trivial, one_mulVec] at h
    have hmuw : (![1, 3] : Fin 2 → ℝ) ⬝ᵥ w = w 0 + 3 * w 1 := by
      show (∑ k, (![1, 3] : Fin 2 → ℝ) k * w k) = w 0 + 3 * w 1
      rw [Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_mul]
    have hwww : w ⬝ᵥ w = (w 0) ^ 2 + (w 1) ^ 2 := by
      show (∑ k, w k * w k) = (w 0) ^ 2 + (w 1) ^ 2
      rw [Fin.sum_univ_two]
      ring
    have hrhs : ((5 / 2 : ℝ) - 0) / Real.sqrt (10 / 16) = Real.sqrt 10 := by
      have h10nn : (0 : ℝ) ≤ 10 := by norm_num
      have h10ne : Real.sqrt (10 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
      have hsqrt10 : Real.sqrt (10 / 16 : ℝ) = Real.sqrt 10 / 4 := by
        have heq : (10 / 16 : ℝ) = 10 / 4 ^ 2 := by norm_num
        rw [heq, Real.sqrt_div h10nn, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 4)]
      have hfrac : (5 / 2 : ℝ) / (Real.sqrt 10 / 4) = 10 / Real.sqrt 10 := by
        rw [div_div_eq_mul_div]
        norm_num
      rw [sub_zero, hsqrt10, hfrac, div_eq_iff h10ne]
      exact (Real.mul_self_sqrt h10nn).symm
    unfold sharpeRatio
    rw [one_mulVec, one_mulVec, hmuw, hmuvM, hwMvM, hrhs, sub_zero, hwww]
    by_cases hnum : w 0 + 3 * w 1 ≤ 0
    · have hsqrtQ : (0 : ℝ) < Real.sqrt ((w 0) ^ 2 + (w 1) ^ 2) := by
        apply Real.sqrt_pos.mpr
        rw [← hwww]
        exact hww
      have hle : (w 0 + 3 * w 1) / Real.sqrt ((w 0) ^ 2 + (w 1) ^ 2) ≤ 0 := by
        rw [div_le_iff₀ hsqrtQ, zero_mul]
        exact hnum
      have hnn : (0 : ℝ) ≤ Real.sqrt 10 := Real.sqrt_nonneg _
      linarith
    · push Not at hnum
      have hsqrtQ : (0 : ℝ) < Real.sqrt ((w 0) ^ 2 + (w 1) ^ 2) := by
        apply Real.sqrt_pos.mpr
        rw [← hwww]
        exact hww
      rw [div_le_iff₀ hsqrtQ]
      have hsq : (w 0 + 3 * w 1) ^ 2
          ≤ (Real.sqrt 10 * Real.sqrt ((w 0) ^ 2 + (w 1) ^ 2)) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 10),
          Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (w 0) ^ 2 + (w 1) ^ 2)]
        nlinarith [sq_nonneg (3 * w 0 - w 1)]
      have hMnn : (0 : ℝ) ≤ Real.sqrt 10 * Real.sqrt ((w 0) ^ 2 + (w 1) ^ 2) :=
        mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      nlinarith [hsq, hnum, hMnn]
  exact securityMarketLine hS ![1, 3] 0 hwM hprem heff 1

end MathlibExtTest.CAPM
