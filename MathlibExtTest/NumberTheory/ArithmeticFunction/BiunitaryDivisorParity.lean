/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Basic
import MathlibExt.NumberTheory.ArithmeticFunction.BiunitaryDivisorParity

open MetaMathlibExt

-- The power-of-two case includes exponent zero and a square with its middle divisor omitted.
example : Odd (sigmaBiunitary 1) :=
  (odd_sigmaBiunitary_iff 1 (by decide)).2 ⟨0, rfl⟩

example : Odd (sigmaBiunitary 4) :=
  (odd_sigmaBiunitary_iff 4 (by decide)).2 ⟨2, rfl⟩

-- In an odd square the middle divisor is again omitted, leaving an even sum.
example : sigmaBiunitary 9 = 10 := by decide

-- An odd factor of a power of two would have to divide 2 itself.
private theorem not_odd_sigmaBiunitary_of_three_dvd (n : ℕ) (hn : 0 < n) (h3 : 3 ∣ n) :
    ¬ Odd (sigmaBiunitary n) := by
  rw [odd_sigmaBiunitary_iff n hn]
  rintro ⟨k, rfl⟩
  exact (by decide : ¬ (3 : ℕ) ∣ 2) (Nat.Prime.dvd_of_dvd_pow (by decide) h3)

example : ¬ Odd (sigmaBiunitary 9) := not_odd_sigmaBiunitary_of_three_dvd 9 (by decide) (by decide)

-- Multiplying a power of two by 3 changes the parity, for every exponent.
example (k : ℕ) : Odd (sigmaBiunitary (2 ^ k)) ∧ ¬ Odd (sigmaBiunitary (3 * 2 ^ k)) := by
  have hk : 0 < (2 : ℕ) ^ k := Nat.pow_pos (by decide)
  exact ⟨(odd_sigmaBiunitary_iff _ hk).2 ⟨k, rfl⟩,
    not_odd_sigmaBiunitary_of_three_dvd _ (Nat.mul_pos (by decide) hk) ⟨2 ^ k, rfl⟩⟩

example : sigmaBiunitary 12 = 20 := by decide

example : ¬ Odd (sigmaBiunitary 12) :=
  not_odd_sigmaBiunitary_of_three_dvd 12 (by decide) (by decide)

-- A client can use the public multiplicativity theorem through the standard API.
example : sigmaBiunitary (9 * 10) = sigmaBiunitary 9 * sigmaBiunitary 10 := by
  simpa only [sigmaBiunitaryArithmeticFunction_apply] using
    isMultiplicative_sigmaBiunitaryArithmeticFunction.map_mul_of_coprime
      (by decide : Nat.Coprime 9 10)

-- `90 = 2 * 3^2 * 5` has two distinct odd prime factors; the bound is sharp.
example : 4 ∣ sigmaBiunitary 90 := by
  have hcard : (90 : ℕ).primeFactors.card = 3 := by
    rw [show (90 : ℕ) = 2 * (3 ^ 2 * 5) by decide,
      Nat.primeFactors_mul (a := 2) (b := 3 ^ 2 * 5) (by decide) (by decide),
      Nat.primeFactors_mul (a := 3 ^ 2) (b := 5) (by decide) (by decide),
      Nat.primeFactors_prime_pow (k := 2) (by decide) Nat.prime_three,
      Nat.prime_two.primeFactors, Nat.prime_five.primeFactors]
    decide
  simpa only [hcard, show (2 : ℕ) ^ (3 - 1) = 4 by decide] using
    two_pow_card_primeFactors_sub_one_dvd_sigmaBiunitary_of_even 90 (by decide) (by decide)

example : ¬ 8 ∣ sigmaBiunitary 90 := by decide

-- For a power of two the exponent drops to zero, and the divisor sum need not be even.
example : 1 ∣ sigmaBiunitary 16 := by
  have hcard : (16 : ℕ).primeFactors.card = 1 := by
    rw [show (16 : ℕ) = 2 ^ 4 by decide,
      Nat.primeFactors_prime_pow (k := 4) (by decide) Nat.prime_two, Finset.card_singleton]
  simpa only [hcard, Nat.sub_self, pow_zero] using
    two_pow_card_primeFactors_sub_one_dvd_sigmaBiunitary_of_even 16 (by decide) (by decide)

example : ¬ 2 ∣ sigmaBiunitary 16 := by decide
