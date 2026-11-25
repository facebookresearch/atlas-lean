/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.UnitaryDivisorCount

namespace MetaMathlibExt

-- The empty set of prime factors gives one divisor.
example : (Nat.unitaryDivisors 1).card = 1 := by
  simpa only [Nat.primeFactors_one, Finset.card_empty, pow_zero] using
    card_unitaryDivisors (n := 1) (hn := by decide)

-- A repeated prime still contributes just two choices.
example : (Nat.unitaryDivisors 8).card = 2 := by
  have hFactors : (8 : ℕ).primeFactors = {2} :=
    Nat.primeFactors_prime_pow (k := 3) (by decide) Nat.prime_two
  rw [card_unitaryDivisors (n := 8) (hn := by decide), hFactors, Finset.card_singleton, pow_one]

private theorem primeFactors_twelve : (12 : ℕ).primeFactors = {2, 3} := by
  have hFour : (4 : ℕ).primeFactors = {2} :=
    Nat.primeFactors_prime_pow (k := 2) (by decide) Nat.prime_two
  change (4 * 3 : ℕ).primeFactors = _
  rw [Nat.primeFactors_mul (by decide) (by decide), hFour, Nat.prime_three.primeFactors]
  decide

example : (Nat.unitaryDivisors 12).card = 4 := by
  rw [card_unitaryDivisors (n := 12) (hn := by decide), primeFactors_twelve]
  decide

-- The full prime powers are 4 and 3, not 2 and 3.
example : 1 ∈ Nat.unitaryDivisors 12 ∧ 3 ∈ Nat.unitaryDivisors 12 ∧
    4 ∈ Nat.unitaryDivisors 12 ∧ 12 ∈ Nat.unitaryDivisors 12 ∧
    2 ∉ Nat.unitaryDivisors 12 ∧ 6 ∉ Nat.unitaryDivisors 12 := by
  simp only [Nat.mem_unitaryDivisors]
  decide

example : (Nat.unitaryDivisors 60).card = 8 := by
  have hFactors : (60 : ℕ).primeFactors = {2, 3, 5} := by
    change (12 * 5 : ℕ).primeFactors = _
    rw [Nat.primeFactors_mul (by decide) (by decide), primeFactors_twelve,
      Nat.prime_five.primeFactors]
    decide
  rw [card_unitaryDivisors (n := 60) (hn := by decide), hFactors]
  decide

-- At one the product is empty, and the only unitary divisor is one.
example : ∑ d ∈ Nat.unitaryDivisors 1, d ^ 2 = 1 := by
  simpa only [Nat.primeFactors_one, Finset.prod_empty] using
    sum_sq_unitaryDivisors (n := 1) (hn := by decide)

-- The factors are 1 + 4² and 1 + 3², for the unitary divisors 1, 3, 4 and 12.
example : ∑ d ∈ Nat.unitaryDivisors 12, d ^ 2 = 170 := by
  have hFour : (4 : ℕ).factorization = Finsupp.single 2 2 := by
    exact Nat.prime_two.factorization_pow (k := 2)
  have hTwelve : (12 : ℕ).factorization = Finsupp.single 2 2 + Finsupp.single 3 1 := by
    change (4 * 3 : ℕ).factorization = _
    rw [Nat.factorization_mul (by decide) (by decide), hFour, Nat.prime_three.factorization]
  rw [sum_sq_unitaryDivisors (n := 12) (hn := by decide), primeFactors_twelve, hTwelve,
    Finset.prod_insert (by decide : (2 : ℕ) ∉ ({3} : Finset ℕ)), Finset.prod_singleton]
  simp

end MetaMathlibExt
