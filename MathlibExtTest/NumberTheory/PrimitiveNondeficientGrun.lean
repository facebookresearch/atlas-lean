/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic.NormNum
import MathlibExt.NumberTheory.PrimitiveNondeficientGrun

/-! # Tests for Grün's bounds -/

open MathlibExt.NumberTheory.PrimitiveNondeficientWanted

-- The perfect number 6 has the least possible count when the least prime is 2.
example : 1 < ((6 : ℕ).primeFactors.card : ℚ) := by
  have hn : IsNondeficient 6 := ⟨by decide, by decide⟩
  have hp : 2 ∈ (6 : ℕ).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Nat.prime_two, by decide, by decide⟩
  have hmin : ∀ q ∈ (6 : ℕ).primeFactors, 2 ≤ q :=
    fun _ hq => (Nat.prime_of_mem_primeFactors hq).two_le
  convert (grun_bounds_of_isNondeficient 6 2 hn hp hmin).1 using 1
  norm_num

-- The odd non-deficient number 945 = 3 ^ 3 * 5 * 7 attains the rounded first bound.
example : (5 : ℚ) / 2 < ((945 : ℕ).primeFactors.card : ℚ) := by
  have hpf : (945 : ℕ).primeFactors = {3, 5, 7} := by
    rw [show (945 : ℕ) = 3 ^ 3 * 5 * 7 by decide,
      Nat.primeFactors_mul (by decide) (by decide), Nat.primeFactors_mul (by decide) (by decide),
      Nat.primeFactors_pow 3 (by decide), Nat.prime_three.primeFactors,
      Nat.prime_five.primeFactors, (by decide : Nat.Prime 7).primeFactors]
    decide
  have hn : IsNondeficient 945 := by
    refine ⟨by decide, ?_⟩
    rw [← ArithmeticFunction.sigma_one_apply, show (945 : ℕ) = 3 ^ 3 * 5 ^ 1 * 7 ^ 1 by decide,
      ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime
        (show (3 ^ 3 * 5 ^ 1 : ℕ).Coprime (7 ^ 1) by decide),
      ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime
        (show (3 ^ 3 : ℕ).Coprime (5 ^ 1) by decide),
      ArithmeticFunction.sigma_one_apply_prime_pow Nat.prime_three,
      ArithmeticFunction.sigma_one_apply_prime_pow Nat.prime_five,
      ArithmeticFunction.sigma_one_apply_prime_pow (by decide : Nat.Prime 7)]
    norm_num [Finset.sum_range_succ]
  have hp : 3 ∈ (945 : ℕ).primeFactors := by rw [hpf]; decide
  have hmin : ∀ q ∈ (945 : ℕ).primeFactors, 3 ≤ q := by
    rw [hpf]
    intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl <;> decide
  have h := (grun_bounds_of_isNondeficient 945 3 hn hp hmin).1
  norm_num at h ⊢
  exact h

-- With least prime 5, the second conclusion rules out the borderline count of six.
example (n : ℕ) (hn : IsNondeficient n) (hp : 5 ∈ n.primeFactors)
    (hmin : ∀ q ∈ n.primeFactors, 5 ≤ q) : 7 ≤ n.primeFactors.card :=
  (grun_bounds_of_isNondeficient n 5 hn hp hmin).2 le_rfl
