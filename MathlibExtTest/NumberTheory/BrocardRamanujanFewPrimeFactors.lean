/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.BrocardRamanujanFewPrimeFactors

open MetaMathlibExt Nat

-- The finiteness theorem applies at the minimum threshold.
example : {p : ℕ × ℕ | p.1 ! + 1 = p.2 ^ 2 ∧
    ((p.2 - 1).primeFactors.card < 2 ∨ (p.2 + 1).primeFactors.card < 2)}.Finite :=
  brocardRamanujan_fewPrimeFactors_finite 2 le_rfl

-- For `(4, 5)` and `l = 2`, only `x - 1 = 4` qualifies.
example : ((4, 5) : ℕ × ℕ) ∈ {p : ℕ × ℕ | p.1 ! + 1 = p.2 ^ 2 ∧
    ((p.2 - 1).primeFactors.card < 2 ∨ (p.2 + 1).primeFactors.card < 2)} := by
  refine ⟨by decide, Or.inl ?_⟩
  change (4 : ℕ).primeFactors.card < 2
  rw [show (4 : ℕ) = 2 ^ 2 by decide, primeFactors_prime_pow (k := 2) (by decide) prime_two]
  simp

example : 2 ≤ (6 : ℕ).primeFactors.card := by
  rw [show (6 : ℕ) = 2 * 3 by decide,
    primeFactors_mul (a := 2) (b := 3) (by decide) (by decide)]
  simp [prime_two, prime_three, Finset.card_insert_of_notMem]

-- For `(7, 71)` and `l = 3`, only `x + 1 = 72` qualifies.
example : ((7, 71) : ℕ × ℕ) ∈ {p : ℕ × ℕ | p.1 ! + 1 = p.2 ^ 2 ∧
    ((p.2 - 1).primeFactors.card < 3 ∨ (p.2 + 1).primeFactors.card < 3)} := by
  refine ⟨by decide, Or.inr ?_⟩
  change (72 : ℕ).primeFactors.card < 3
  rw [show (72 : ℕ) = 2 ^ 3 * 3 ^ 2 by decide,
    primeFactors_mul (a := 2 ^ 3) (b := 3 ^ 2) (by decide) (by decide),
    primeFactors_prime_pow (k := 3) (by decide) prime_two,
    primeFactors_prime_pow (k := 2) (by decide) prime_three]
  simp [Finset.card_insert_of_notMem]

example : 3 ≤ (70 : ℕ).primeFactors.card := by
  rw [show (70 : ℕ) = 2 * (5 * 7) by decide,
    primeFactors_mul (a := 2) (b := 5 * 7) (by decide) (by decide),
    primeFactors_mul (a := 5) (b := 7) (by decide) (by decide)]
  simp [prime_two, prime_five, prime_seven, Finset.card_insert_of_notMem]
