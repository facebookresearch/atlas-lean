/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.OddTwoPrimeFactorsDeficient

/-! # Tests for deficiency with two distinct prime factors -/

open MathlibExt.NumberTheory.PrimitiveNondeficientWanted

-- Squarefree case: 15 = 3 · 5.
example : ∑ d ∈ Nat.divisors 15, d < 2 * 15 := by
  apply deficient_of_odd_card_primeFactors_eq_two 15 ⟨7, rfl⟩
  change (3 * 5 : ℕ).primeFactors.card = 2
  rw [Nat.primeFactors_mul (by decide) (by decide), Nat.prime_three.primeFactors,
    Nat.prime_five.primeFactors]
  decide

-- A repeated prime: 45 = 3² · 5 still has only two distinct prime factors.
example : ∑ d ∈ Nat.divisors 45, d < 2 * 45 := by
  apply deficient_of_odd_card_primeFactors_eq_two 45 ⟨22, rfl⟩
  change (3 ^ 2 * 5 : ℕ).primeFactors.card = 2
  rw [Nat.primeFactors_mul (by decide) (by decide), Nat.primeFactors_pow 3 (by decide),
    Nat.prime_three.primeFactors, Nat.prime_five.primeFactors]
  decide

-- Without the oddness hypothesis, 6 is a counterexample: it is perfect.
example : Even (6 : ℕ) ∧ (6 : ℕ).primeFactors.card = 2 ∧
    (∑ d ∈ Nat.divisors 6, d) = 2 * 6 := by
  refine ⟨⟨3, rfl⟩, ?_, ?_⟩
  · change (2 * 3 : ℕ).primeFactors.card = 2
    rw [Nat.primeFactors_mul (by decide) (by decide), Nat.prime_two.primeFactors,
      Nat.prime_three.primeFactors]
    decide
  · rw [← Nat.filter_dvd_eq_divisors (by decide : (6 : ℕ) ≠ 0)]
    decide
