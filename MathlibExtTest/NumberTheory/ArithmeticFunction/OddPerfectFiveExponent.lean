/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic.NormNum
import MathlibExt.NumberTheory.ArithmeticFunction.OddPerfectFiveExponent

open ArithmeticFunction Finset

-- Check both exact divisor sums and their strict excess over twice the input.
example : (∑ d ∈ (70785 : ℕ).divisors, d) = 145236 ∧ 2 * 70785 < 145236 := by
  refine ⟨?_, by decide⟩
  rw [← sigma_one_apply, ← show (3 ^ 2 * (5 ^ 1 * (11 ^ 2 * 13 ^ 1)) : ℕ) = 70785 by norm_num]
  rw [isMultiplicative_sigma.map_mul_of_coprime
      (by decide : Nat.Coprime (3 ^ 2) (5 ^ 1 * (11 ^ 2 * 13 ^ 1))),
    isMultiplicative_sigma.map_mul_of_coprime
      (by decide : Nat.Coprime (5 ^ 1) (11 ^ 2 * 13 ^ 1)),
    isMultiplicative_sigma.map_mul_of_coprime (by decide : Nat.Coprime (11 ^ 2) (13 ^ 1)),
    sigma_one_apply_prime_pow (p := 3) (by decide), sigma_one_apply_prime_pow (p := 5) (by decide),
    sigma_one_apply_prime_pow (p := 11) (by decide), sigma_one_apply_prime_pow (p := 13) (by decide)]
  norm_num [sum_range_succ]

example : (∑ d ∈ (245025 : ℕ).divisors, d) = 498883 ∧ 2 * 245025 < 498883 := by
  refine ⟨?_, by decide⟩
  rw [← sigma_one_apply, ← show (3 ^ 4 * (5 ^ 2 * 11 ^ 2) : ℕ) = 245025 by norm_num]
  rw [isMultiplicative_sigma.map_mul_of_coprime (by decide : Nat.Coprime (3 ^ 4) (5 ^ 2 * 11 ^ 2)),
    isMultiplicative_sigma.map_mul_of_coprime (by decide : Nat.Coprime (5 ^ 2) (11 ^ 2)),
    sigma_one_apply_prime_pow (p := 3) (by decide), sigma_one_apply_prime_pow (p := 5) (by decide),
    sigma_one_apply_prime_pow (p := 11) (by decide)]
  norm_num [sum_range_succ]

-- The hypotheses are conditional; this does not exhibit an odd perfect number.
example (n : ℕ) (hodd : Odd n) (hperf : n.Perfect) (h165 : 165 ∣ n) :
    n.factorization 5 = 1 :=
  MetaMathlibExt.oddPerfect_factorization_five_eq_one_of_dvd
    (n := n) (hodd := hodd) (hperf := hperf) (h165 := h165)
