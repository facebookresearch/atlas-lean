/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ArithmeticFunction.BiunitaryTriperfect
import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Data.Nat.PrimeFin

namespace MathlibExtTest.NumberTheory.ArithmeticFunction.BiunitaryTriperfect

open MetaMathlibExt

-- The odd number `15 = 3 * 5` has two distinct prime factors, so `4 ∣ σ**(15)`.
example : 4 ∣ sigmaBiunitary 15 := by
  have hcard : (15 : ℕ).primeFactors.card = 2 := by
    rw [show (15 : ℕ) = 3 * 5 by rfl, Nat.primeFactors_mul (by decide) (by decide),
      Nat.Prime.primeFactors (by decide : Nat.Prime 3),
      Nat.Prime.primeFactors (by decide : Nat.Prime 5)]
    decide
  have h := two_pow_card_primeFactors_dvd_sigmaBiunitary_of_odd 15 ⟨7, rfl⟩
  rw [hcard] at h
  simpa using h

-- An odd number with at least two distinct prime factors has `4 ∣ σ**(n)`.
example (n : ℕ) (hn : Odd n) (hω : 2 ≤ n.primeFactors.card) : 4 ∣ sigmaBiunitary n := by
  have h := two_pow_card_primeFactors_dvd_sigmaBiunitary_of_odd n hn
  have h4 : (4 : ℕ) = 2 ^ 2 := rfl
  rw [h4]
  exact (pow_dvd_pow 2 hω).trans h

-- The biunitary divisor sum of an odd prime power is even.
example (p e : ℕ) (hp : p.Prime) (hodd : Odd p) (he : 1 ≤ e) :
    Even (sigmaBiunitary (p ^ e)) := by
  have hn : Odd (p ^ e) := hodd.pow
  have h := two_pow_card_primeFactors_dvd_sigmaBiunitary_of_odd (p ^ e) hn
  have hcard : (p ^ e).primeFactors.card = 1 := by
    rw [Nat.primeFactors_prime_pow (by omega) hp]
    simp
  rw [hcard, pow_one] at h
  exact even_iff_two_dvd.mpr h

end MathlibExtTest.NumberTheory.ArithmeticFunction.BiunitaryTriperfect
