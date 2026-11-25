/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum
import MathlibExt.NumberTheory.SumSquaredDivisorsProduct

namespace MetaMathlibExt

-- At one the products are empty, and the upper bound is attained with equality.
example :
    (ArithmeticFunction.sigma 2 1 : ℚ) = 1 ∧
      (ArithmeticFunction.sigma 2 1 : ℚ) / (1 : ℚ) ^ 2 =
        ∏ p ∈ (1 : ℕ).primeFactors, (p : ℚ) ^ 2 / (p ^ 2 - 1) := by
  obtain ⟨hSum, hRatio, _⟩ := sigma_two_prod_formulas (n := 1) (hn := by decide)
  rw [Nat.primeFactors_one, Finset.prod_empty] at hSum hRatio ⊢
  exact ⟨hSum, hRatio⟩

-- At four the only prime factor contributes three geometric terms: 1, 4, and 16.
example :
    (ArithmeticFunction.sigma 2 4 : ℚ) = 21 ∧
      (ArithmeticFunction.sigma 2 4 : ℚ) / (4 : ℚ) ^ 2 = 21 / 16 ∧
      (ArithmeticFunction.sigma 2 4 : ℚ) / (4 : ℚ) ^ 2 < 4 / 3 := by
  have hFactors : (4 : ℕ).primeFactors = {2} :=
    Nat.primeFactors_prime_pow (k := 2) (by decide) Nat.prime_two
  have hExp : (4 : ℕ).factorization 2 = 2 := Nat.factorization_pow_self (n := 2) Nat.prime_two
  obtain ⟨hSum, hRatio, hBound⟩ := sigma_two_prod_formulas (n := 4) (hn := by decide)
  refine ⟨?_, ?_, ?_⟩
  · norm_num [hFactors, hExp] at hSum
    exact hSum
  · norm_num [hFactors, hExp] at hRatio ⊢
    exact hRatio
  · specialize hBound (by decide)
    norm_num [hFactors] at hBound ⊢
    exact hBound

-- At twelve the exponents differ: the two factors come from four and three.
example :
    (ArithmeticFunction.sigma 2 12 : ℚ) = 210 ∧
      (ArithmeticFunction.sigma 2 12 : ℚ) / (12 : ℚ) ^ 2 = 35 / 24 ∧
      (ArithmeticFunction.sigma 2 12 : ℚ) / (12 : ℚ) ^ 2 < 3 / 2 := by
  have hFour : (4 : ℕ).primeFactors = {2} :=
    Nat.primeFactors_prime_pow (k := 2) (by decide) Nat.prime_two
  have hFactors : (12 : ℕ).primeFactors = {2, 3} := by
    change (4 * 3 : ℕ).primeFactors = _
    rw [Nat.primeFactors_mul (by decide) (by decide), hFour, Nat.prime_three.primeFactors]
    decide
  have hFourExp : (4 : ℕ).factorization 2 = 2 := Nat.factorization_pow_self (n := 2) Nat.prime_two
  have hExpTwo : (12 : ℕ).factorization 2 = 2 := by
    change (4 * 3 : ℕ).factorization 2 = 2
    rw [Nat.factorization_mul (by decide) (by decide), Finsupp.add_apply, hFourExp,
      Nat.factorization_eq_zero_of_not_dvd (by decide : ¬2 ∣ 3), Nat.add_zero]
  have hExpThree : (12 : ℕ).factorization 3 = 1 := by
    change (4 * 3 : ℕ).factorization 3 = 1
    rw [Nat.factorization_mul (by decide) (by decide), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd (by decide : ¬3 ∣ 4), Nat.prime_three.factorization_self,
      Nat.zero_add]
  have hTwoNotMem : (2 : ℕ) ∉ ({3} : Finset ℕ) := by decide
  obtain ⟨hSum, hRatio, hBound⟩ := sigma_two_prod_formulas (n := 12) (hn := by decide)
  refine ⟨?_, ?_, ?_⟩
  · norm_num [hFactors, Finset.prod_insert hTwoNotMem, hExpTwo, hExpThree] at hSum
    exact hSum
  · norm_num [hFactors, Finset.prod_insert hTwoNotMem, hExpTwo, hExpThree] at hRatio ⊢
    exact hRatio
  · specialize hBound (by decide)
    norm_num [hFactors, Finset.prod_insert hTwoNotMem] at hBound ⊢
    exact hBound

end MetaMathlibExt
