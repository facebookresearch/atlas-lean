/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Int.ModEq
import MathlibExt.NumberTheory.OddPartFactorialTwoAdic

/-!
# Tests for dyadic odd parts, odd products, and normalized odd double factorials
-/

open MetaMathlibExt

-- At the first admissible exponent the upper endpoint is the only preimage of one.
example : Set.BijOn oddPart ({2} : Set ℕ) {1} := by
  have hdom : dyadicUpperHalf 1 = {2} := by decide
  have himg : oddBelowTwoPow 1 = {1} := by decide
  simpa only [hdom, himg, Finset.coe_singleton] using
    oddPart_bijOn_upperHalf_oddSet 1 (by decide)

-- Scaling three by four gives its unique representative in (8, 16].
example {n : ℕ} (hn : n ∈ dyadicUpperHalf 4) : oddPart n = 3 ↔ n = 12 := by
  have h12 : 12 ∈ dyadicUpperHalf 4 := by decide
  have hpart : oddPart 12 = 3 :=
    Nat.ordCompl_pow_mul_of_not_dvd 2 Nat.prime_two (show ¬ 2 ∣ 3 by decide)
  rw [← hpart]
  exact ⟨(oddPart_bijOn_upperHalf_oddSet 4 (by decide)).injOn hn h12, congrArg oddPart⟩

-- The dyadic interval is empty when the exponent is zero.
example : oddDoubleFactorial 0 = 1 := by decide

-- The first division would already be inexact at the excluded exponent.
example : ¬ (4 : ℤ) ∣ (oddDoubleFactorial 2 : ℤ) - 1 := by decide

-- At the first admissible exponent the quotients differ but agree modulo four.
example : ((oddDoubleFactorial 3 : ℤ) - 1) / 8 = 13 ∧
    ((oddDoubleFactorial 4 : ℤ) - 1) / 16 = 126689 := by decide

example : (4 : ℤ) ∣ ((oddDoubleFactorial 3 : ℤ) - 1) / 8 -
    ((oddDoubleFactorial 4 : ℤ) - 1) / 16 :=
  (oddDoubleFactorial_normalized_congr 3 (by decide)).2.2

-- The congruence fails just below the lower bound.
example : ¬ (8 : ℤ) ∣ ((∏ i ∈ oddBelowTwoPow 2, i : ℕ) : ℤ) - 5 := by decide

-- At the lower bound the product is 105, with residue 9 modulo 16.
example : ((∏ i ∈ oddBelowTwoPow 3, i : ℕ) : ℤ) % 16 = 9 :=
  (Int.modEq_of_dvd (oddSet_product_congr 3 (by decide))).symm

-- The shift congruence fails just below the lower bound: 1 and 3 differ modulo four.
example : ¬ (2 : ℤ) ^ (2 * 1) ∣ ((∏ i ∈ oddBelowTwoPow 1, i : ℕ) : ℤ) -
    ∏ i ∈ oddBelowTwoPow 1, ((2 ^ 1 + i : ℕ) : ℤ) := by decide

-- Shifting 1, 3, 5, 7 by eight keeps the residue 105 ≡ 41 modulo 64.
example : (∏ i ∈ oddBelowTwoPow 3, ((2 ^ 3 + i : ℕ) : ℤ)) % 64 = 41 :=
  Eq.trans (Int.modEq_of_dvd (oddSet_product_congr_shift 3 (by decide))) (by decide)

-- Below the exponent bound there are only two roots of one.
example : ({i ∈ oddBelowTwoPow 2 | i ^ 2 % 4 = 1}).card = 2 := by decide

-- At the bound every odd residue squares to one.
example : ({i ∈ oddBelowTwoPow 3 | i ^ 2 % 8 = 1}).card = 4 :=
  square_mod_twoPower_fiber_card 3 (by decide) 1 (by decide) (by decide)

-- The other admissible residue modulo sixteen has two roots in each odd class modulo four.
example : {i ∈ oddBelowTwoPow 4 | i ^ 2 % 16 = 9} = {3, 5, 11, 13} := by decide

-- Just below the exponent bound the congruence fails: `od(2!) = 1` and `od(4!) = 3`.
example : ¬ (2 : ℤ) ^ 2 ∣ (oddPart (Nat.factorial (2 ^ (2 - 1))) : ℤ) -
    (oddPart (Nat.factorial (2 ^ 2)) : ℤ) := by
  have h₁ : oddPart (Nat.factorial (2 ^ (2 - 1))) = 1 := by
    rw [show Nat.factorial (2 ^ (2 - 1)) = 2 ^ 1 * 1 by decide]
    exact Nat.ordCompl_pow_mul_of_not_dvd 1 Nat.prime_two (by decide)
  have h₂ : oddPart (Nat.factorial (2 ^ 2)) = 3 := by
    rw [show Nat.factorial (2 ^ 2) = 2 ^ 3 * 3 by decide]
    exact Nat.ordCompl_pow_mul_of_not_dvd 3 Nat.prime_two (by decide)
  rw [h₁, h₂]
  decide

-- At the lower bound `od(4!) = 3`, so the odd part `315` of `8!` is `3` modulo eight.
example : (oddPart (Nat.factorial (2 ^ 3)) : ℤ) % 8 = 3 := by
  have h₁ : oddPart (Nat.factorial (2 ^ (3 - 1))) = 3 := by
    rw [show Nat.factorial (2 ^ (3 - 1)) = 2 ^ 3 * 3 by decide]
    exact Nat.ordCompl_pow_mul_of_not_dvd 3 Nat.prime_two (by decide)
  have h := oddPart_factorial_congr_previous 3 le_rfl
  rw [h₁] at h
  exact Int.modEq_of_dvd h

-- At the first admissible exponent the four copies are all ones.
example : reverseESymm 1 (fourCopiesOneModEightBelowTwoPow 3) = 4 := by decide

-- The value at the first admissible exponent is not divisible by eight.
example : ¬ (8 : ℤ) ∣ reverseESymm 1 (fourCopiesOneModEightBelowTwoPow 3) := by decide

-- At the next exponent the value is 29160, with residue 8 modulo 16.
example : reverseESymm 1 (fourCopiesOneModEightBelowTwoPow 4) = 29160 := by decide

-- The four-copies congruence at the next exponent but one.
example : (32 : ℤ) ∣ reverseESymm 1 (fourCopiesOneModEightBelowTwoPow 5) - 16 :=
  reverseESymm_fourCopies_oneModEight_congr 5 (by decide)
