/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.SZumkellerThreeLeCardPrimeFactorsOfIsSZumkellerEven

/-! # Tests for even s-Zumkeller numbers having at least three prime factors -/

namespace MathlibExtTest.NumberTheory.SZumkellerThreeLeCardPrimeFactorsOfIsSZumkellerEven

open MetaMathlibExt

-- `60` is even and s-Zumkeller, so it has at least three prime factors.
example : 3 ≤ (60 : ℕ).primeFactors.card :=
  three_le_card_primeFactors_of_isSZumkeller_even 60 isSZumkeller_sixty (by decide)

-- An even number with fewer than three prime factors is not s-Zumkeller.
example (n : ℕ) (he : Even n) (hcard : n.primeFactors.card < 3) : ¬ IsSZumkeller n := by
  intro h
  exact absurd (three_le_card_primeFactors_of_isSZumkeller_even n h he) (by omega)

-- `12 = 2² · 3` has only two prime factors, so it is not s-Zumkeller.
example : ¬ IsSZumkeller 12 := by
  intro h
  have hsub : (12 : ℕ).primeFactors ⊆ {2, 3} := by
    intro p hp
    have h12 : (12 : ℕ) = 2 ^ 2 * 3 := by norm_num
    rw [h12, Nat.primeFactors_mul (by norm_num) (by norm_num),
      Nat.primeFactors_prime_pow (by norm_num) Nat.prime_two,
      Nat.Prime.primeFactors Nat.prime_three] at hp
    simpa using hp
  have hcard : (12 : ℕ).primeFactors.card ≤ 2 := by
    calc (12 : ℕ).primeFactors.card ≤ ({2, 3} : Finset ℕ).card := Finset.card_le_card hsub
      _ = 2 := by decide
  exact absurd (three_le_card_primeFactors_of_isSZumkeller_even 12 h (by decide)) (by omega)

end MathlibExtTest.NumberTheory.SZumkellerThreeLeCardPrimeFactorsOfIsSZumkellerEven
