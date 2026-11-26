/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ModularInverseProductMeanCoprimeSumMulAdditiveCharacter

/-! # Tests for the weighted additive character sum over reduced residues -/

namespace MathlibExtTest.NumberTheory.ModularInverseProductMeanCoprimeSumMulAdditiveCharacter

open Complex Finset MetaMathlibExt

-- At modulus two and frequency one the coprime sum has the single term `b = 1` of value `-1`.
example : ∑ b ∈ Icc (1 : ℕ) 2 with Nat.Coprime b 2,
    (b : ℂ) * exp (2 * Real.pi * I * (-((1 : ℕ) * b : ℂ)) / (2 : ℕ)) = -1 := by
  have h := coprime_sum_mul_additive_character (n := 2) (k := 1) (by decide) (by decide)
  rw [h]
  rw [show Nat.divisors 2 = ({1, 2} : Finset ℕ) by decide]
  rw [show Finset.filter (fun d => ¬ (2 / d) ∣ 1) ({1, 2} : Finset ℕ) = {1} by decide]
  rw [show Finset.filter (fun d => d < 2 ∧ (2 / d) ∣ 1) ({1, 2} : Finset ℕ) = ∅ by decide]
  rw [Finset.sum_singleton, Finset.sum_empty]
  rw [show (2 : ℕ) / 1 = 2 by decide, ArithmeticFunction.moebius_apply_one]
  norm_num only [Nat.cast_one, Nat.cast_ofNat, Int.cast_one]
  rw [show 2 * (Real.pi : ℂ) * I * (-(1 : ℂ)) / (2 : ℂ) = -(Real.pi * I) by ring,
    Complex.exp_neg_pi_mul_I]
  norm_num

-- At modulus two and frequency two only the divisor `d = 1` contributes, giving `1`.
example : ∑ b ∈ Icc (1 : ℕ) 2 with Nat.Coprime b 2,
    (b : ℂ) * exp (2 * Real.pi * I * (-((2 : ℕ) * b : ℂ)) / (2 : ℕ)) = 1 := by
  have h := coprime_sum_mul_additive_character (n := 2) (k := 2) (by decide) (by decide)
  rw [h]
  rw [show Nat.divisors 2 = ({1, 2} : Finset ℕ) by decide]
  rw [show Finset.filter (fun d => ¬ (2 / d) ∣ 2) ({1, 2} : Finset ℕ) = ∅ by decide]
  rw [show Finset.filter (fun d => d < 2 ∧ (2 / d) ∣ 2) ({1, 2} : Finset ℕ) = {1} by decide]
  rw [Finset.sum_empty, Finset.sum_singleton]
  rw [show (2 : ℕ) / 1 = 2 by decide, ArithmeticFunction.moebius_apply_one]
  norm_num only [Nat.cast_one, Nat.cast_ofNat, Int.cast_one]

end MathlibExtTest.NumberTheory.ModularInverseProductMeanCoprimeSumMulAdditiveCharacter
