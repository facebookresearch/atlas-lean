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

private noncomputable def fifthPowerPoly : ℚ[X] := C (4 / 3) * X ^ 3 - C (1 / 3) * X ^ 2

private theorem fifthPowerPoly_eval (n : ℕ) :
    (∑ k ∈ Icc 1 n, (k : ℚ) ^ 5) = fifthPowerPoly.eval ((n * (n + 1) / 2 : ℕ) : ℚ) := by
  have ht (m : ℕ) : ((m * (m + 1) / 2 : ℕ) : ℚ) = (m : ℚ) * (m + 1) / 2 := by
    have h := Nat.cast_choose_two (K := ℚ) (m + 1)
    rw [Nat.choose_two_right, Nat.add_sub_cancel, mul_comm (m + 1) m] at h
    rw [h, Nat.cast_add, Nat.cast_one, add_sub_cancel_right, mul_comm]
  simp only [ht, fifthPowerPoly, eval_sub, eval_mul, eval_C, eval_pow, eval_X]
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
  · norm_num [fifthPowerPoly, coeff_sub, coeff_C_mul, coeff_X_pow, Nat.factorial] at hw ⊢
    exact hw
