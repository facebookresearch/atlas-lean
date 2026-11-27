/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.SuperMZumkellerFactorization
import Mathlib.Data.Nat.PrimeFin

open MathlibExt.NumberTheory.SuperMZumkellerWanted

-- The divisor product of 4 is 8, which has no fixed complementary divisor.
example : IsSuperMZumkeller 4 := by
  rw [isSuperMZumkeller_iff 4 (by decide), show divisorProd 4 = 8 by decide]
  change ∀ p ∈ ((2 : ℕ) ^ 2).primeFactors,
    8 ∣ ((2 : ℕ) ^ 2).factorization p * (Nat.divisors 4).card * (Nat.divisors 8).card
  rw [Nat.primeFactors_prime_pow (by decide) Nat.prime_two]
  intro p hp
  obtain rfl := Finset.mem_singleton.mp hp
  rw [Nat.factorization_pow_self Nat.prime_two]
  decide

-- For n = 2^7 the divisor product is a fourth power, so there is a fixed midpoint.
example : IsSuperMZumkeller ((2 : ℕ) ^ 7) := by
  have hD (a : ℕ) : ((2 : ℕ) ^ a).divisors.card = a + 1 := by
    rw [Nat.divisors_prime_pow Nat.prime_two, Finset.card_map, Finset.card_range]
  have hT : divisorProd ((2 : ℕ) ^ 7) = (2 : ℕ) ^ 28 := by
    apply pow_left_injective (n := 2) (by decide)
    change (divisorProd ((2 : ℕ) ^ 7)) ^ 2 = ((2 : ℕ) ^ 28) ^ 2
    rw [divisorProd_sq _ (by decide), hD, ← pow_mul, ← pow_mul]
  rw [isSuperMZumkeller_iff _ (by decide), hT, hD, hD,
    Nat.primeFactors_prime_pow (by decide) Nat.prime_two]
  intro p hp
  obtain rfl := Finset.mem_singleton.mp hp
  rw [Nat.factorization_pow_self Nat.prime_two]
  decide

-- The lower endpoint n = 2 fails the divisibility condition.
example : ¬ IsSuperMZumkeller 2 := by
  rw [isSuperMZumkeller_iff 2 (by decide), show divisorProd 2 = 2 by decide]
  intro h
  have h2 := h 2 (Nat.mem_primeFactors.mpr ⟨Nat.prime_two, dvd_rfl, by decide⟩)
  rw [Nat.prime_two.factorization_self] at h2
  exact (by decide : ¬ (8 : ℕ) ∣ 1 * (Nat.divisors 2).card * (Nat.divisors 2).card) h2
