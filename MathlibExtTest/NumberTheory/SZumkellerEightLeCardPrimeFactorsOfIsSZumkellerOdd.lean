/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.SZumkellerEightLeCardPrimeFactorsOfIsSZumkellerOdd

/-! # Tests for odd s-Zumkeller numbers divisible by three -/

namespace MathlibExtTest.NumberTheory.SZumkellerEightLeCardPrimeFactorsOfIsSZumkellerOdd

open MetaMathlibExt

-- An odd multiple of 3 with fewer than eight prime factors is not s-Zumkeller.
example (n : ℕ) (ho : Odd n) (h3 : 3 ∣ n) (hlt : n.primeFactors.card < 8) :
    ¬ IsSZumkeller n := fun h =>
  (not_le.mpr hlt) (eight_le_card_primeFactors_of_isSZumkeller_odd n h ho h3)

-- 15 = 3 · 5 has two prime factors, so it is not s-Zumkeller.
example : ¬ IsSZumkeller 15 := by
  intro h
  have h8 := eight_le_card_primeFactors_of_isSZumkeller_odd 15 h (by decide)
    (by decide)
  have hcard : (15 : ℕ).primeFactors.card = 2 := by
    have h : (15 : ℕ) = 3 * 5 := by norm_num
    have h3 : (3 : ℕ) ≠ 0 := by norm_num
    have h5 : (5 : ℕ) ≠ 0 := by norm_num
    have hp3 : Nat.Prime 3 := by decide
    have hp5 : Nat.Prime 5 := by decide
    rw [h, Nat.primeFactors_mul h3 h5, Nat.Prime.primeFactors hp3,
      Nat.Prime.primeFactors hp5]
    decide
  omega

end MathlibExtTest.NumberTheory.SZumkellerEightLeCardPrimeFactorsOfIsSZumkellerOdd
