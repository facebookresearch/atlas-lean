/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.WilsonFaulhaberCoefficients
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Nat.Choose.Cast

/-! # Tests for Faulhaber coefficients and Wilson's congruence -/

open Finset Polynomial MathlibExt.NumberTheory.WilsonFaulhaberWanted

-- The existential statement applies to the smallest odd prime, including the empty sum.
example : ∃ F : ℚ[X], F.eval 0 = 0 ∧ F.eval 3 = 9 := by
  obtain ⟨F, hF⟩ := (faulhaber_coeff_integral_and_wilson 3 1 (by decide) rfl).1
  refine ⟨F, ?_, ?_⟩
  · simpa using (hF 0).symm
  · have hn := (hF 2).symm
    norm_num [show Icc 1 2 = {1, 2} by decide, sum_insert] at hn
    exact hn

-- The explicit cubic power-sum polynomial is `X^2`. Its Wilson difference at `p = 3` is `9 / 2`.
example : (X ^ 2 : ℚ[X]).eval 0 = 0 ∧ (X ^ 2 : ℚ[X]).eval 3 = 9 ∧
    padicNorm 3 (2 - ((X ^ 2 : ℚ[X]).coeff 2 / 2 - 3)) = (3 : ℚ) ^ (-2 : ℤ) := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  refine ⟨by simp, by norm_num, ?_⟩
  have h2 : padicNorm 3 (2 : ℚ) = 1 := (padicNorm.nat_eq_one_iff 2).2 (by decide)
  have h3 : padicNorm 3 (3 : ℚ) = (3 : ℚ)⁻¹ := padicNorm.padicNorm_p_of_prime (p := 3)
  rw [coeff_X_pow, ite_eq_left rfl, show (2 : ℚ) - (1 / 2 - 3) = (3 * 3) / 2 by norm_num]
  simp only [padicNorm.div, padicNorm.mul, h2, h3, div_one]
  norm_num [zpow_neg]

private theorem triangular_cast (n : ℕ) :
    ((n * (n + 1) / 2 : ℕ) : ℚ) = (n : ℚ) * (n + 1) / 2 := by
  have h := Nat.cast_choose_two (K := ℚ) (n + 1)
  rw [Nat.choose_two_right, Nat.add_sub_cancel, mul_comm (n + 1) n] at h
  rw [h, Nat.cast_add, Nat.cast_one, add_sub_cancel_right, mul_comm]

private theorem cubePowerPoly_eval (n : ℕ) :
    (∑ k ∈ Icc 1 n, (k : ℚ) ^ 3) = (X ^ 2 : ℚ[X]).eval ((n * (n + 1) / 2 : ℕ) : ℚ) := by
  simp only [triangular_cast, eval_pow, eval_X]
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [sum_Icc_succ_top (by omega : 1 ≤ n + 1), ih, Nat.cast_succ]
    ring

-- Apply both conclusions to the explicit cubic power-sum polynomial.
example : padicNorm 3 1 ≤ 1 ∧
    padicNorm 3 (2 - (1 / 2 - 3)) ≤ (3 : ℚ) ^ (-2 : ℤ) := by
  obtain ⟨hc, hw⟩ :=
    (faulhaber_coeff_integral_and_wilson 3 1 (by decide) rfl).2 (X ^ 2) cubePowerPoly_eval
  refine ⟨?_, ?_⟩
  · have hi := hc 1 (by decide)
    rw [show (X ^ 2 : ℚ[X]).coeff (1 + 1) = 1 by simp [coeff_X_pow]] at hi
    exact hi
  · have hfac : Nat.factorial (3 - 1) = 2 := by decide
    rw [hfac] at hw
    norm_num [coeff_X_pow] at hw ⊢
    exact hw

private noncomputable def fifthPowerPoly : ℚ[X] := C (4 / 3) * X ^ 3 - C (1 / 3) * X ^ 2

private theorem fifthPowerPoly_eval (n : ℕ) :
    (∑ k ∈ Icc 1 n, (k : ℚ) ^ 5) = fifthPowerPoly.eval ((n * (n + 1) / 2 : ℕ) : ℚ) := by
  simp only [triangular_cast, fifthPowerPoly, eval_sub, eval_mul, eval_C, eval_pow, eval_X]
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [sum_Icc_succ_top (by omega : 1 ≤ n + 1), ih, Nat.cast_succ]
    ring

-- With `p = 5`, the quadratic term is `-1/3` and the cubic term is `4/3`.
example : padicNorm 5 (-1 / 3) ≤ 1 ∧ padicNorm 5 (4 / 3) ≤ 1 ∧
    padicNorm 5 (24 - ((-1 / 3 : ℚ) / 2 - 5)) ≤ (5 : ℚ) ^ (-2 : ℤ) := by
  obtain ⟨hc, hw⟩ :=
    (faulhaber_coeff_integral_and_wilson 5 2 (by decide) rfl).2 fifthPowerPoly fifthPowerPoly_eval
  refine ⟨?_, ?_, ?_⟩
  · simpa [fifthPowerPoly, coeff_sub, coeff_C_mul, coeff_X_pow, neg_div] using hc 1 (by decide)
  · simpa [fifthPowerPoly, coeff_sub, coeff_C_mul, coeff_X_pow] using hc 2 (by decide)
  · have hfac : Nat.factorial (5 - 1) = 24 := by decide
    rw [hfac] at hw
    norm_num [fifthPowerPoly, coeff_sub, coeff_C_mul, coeff_X_pow] at hw ⊢
    exact hw

-- Check the norms independently of the general theorem, using the exact Wilson difference 175 / 6.
example : padicNorm 5 (fifthPowerPoly.coeff 2) = 1 ∧
    padicNorm 5 (fifthPowerPoly.coeff 3) = 1 ∧
    padicNorm 5 (24 - (fifthPowerPoly.coeff 2 / 2 - 5)) = (5 : ℚ) ^ (-2 : ℤ) := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hc2 : fifthPowerPoly.coeff 2 = -(1 / 3) := by
    norm_num [fifthPowerPoly, coeff_sub, coeff_C_mul, coeff_X_pow]
  have hc3 : fifthPowerPoly.coeff 3 = 4 / 3 := by
    norm_num [fifthPowerPoly, coeff_sub, coeff_C_mul, coeff_X_pow]
  have hnorm (n : ℕ) (hn : ¬ 5 ∣ n) : padicNorm 5 (n : ℚ) = 1 :=
    (padicNorm.nat_eq_one_iff n).2 hn
  have h3 : padicNorm 5 (3 : ℚ) = 1 := hnorm 3 (by decide)
  have h4 : padicNorm 5 (4 : ℚ) = 1 := hnorm 4 (by decide)
  have h5 : padicNorm 5 (5 : ℚ) = (5 : ℚ)⁻¹ := padicNorm.padicNorm_p_of_prime (p := 5)
  have h6 : padicNorm 5 (6 : ℚ) = 1 := hnorm 6 (by decide)
  have h7 : padicNorm 5 (7 : ℚ) = 1 := hnorm 7 (by decide)
  rw [hc2, hc3]
  refine ⟨?_, ?_, ?_⟩
  · rw [padicNorm.neg, padicNorm.div, padicNorm.one, h3, div_one]
  · rw [padicNorm.div, h4, h3, div_one]
  · rw [show (24 : ℚ) - (-(1 / 3) / 2 - 5) = (5 * 5) * (7 / 6) by norm_num]
    simp only [padicNorm.mul, padicNorm.div, h5, h7, h6, div_one, mul_one]
    norm_num [zpow_neg]
