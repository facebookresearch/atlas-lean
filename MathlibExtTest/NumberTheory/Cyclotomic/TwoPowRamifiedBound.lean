/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Cyclotomic.TwoPowRamifiedBound
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Prime.Nth

/-! # Tests for the ramified bounds at the exponents two and four -/

namespace MetaMathlibExt

-- At the smallest exponent, two distinct prime factors give 1 + 2 · 2 · 3 = 13.
example {x : ℕ} (hx : 1 < x) (hw : (x ^ 2 - 1).primeFactors.card = 2) : 13 ≤ x ^ 2 := by
  have h := two_pow_trivial_ramified_bound (a := 1) (by decide) hx
  rw [pow_one, hw] at h
  simpa [Finset.prod_range_succ] using h

-- At x = 29, the first term gives equality: 29² − 1 = 4 · 2 · 3 · 5 · 7.
example :
    min (1 + 4 * ∏ i ∈ Finset.range (840 : ℕ).primeFactors.card, Nat.nth Nat.Prime i)
        (1 + ∏ i ∈ Finset.range (840 : ℕ).primeFactors.card, Nat.nth Nat.Prime (i + 1)) =
      29 ^ 2 := by
  apply le_antisymm (two_pow_ramified_bound (a := 1) (x := 29) (by decide) (by decide))
  have hw : (840 : ℕ).primeFactors.card = 4 := by
    rw [show (840 : ℕ) = 2 ^ 3 * 3 * 5 * 7 by decide]
    simp (disch := decide) only [Nat.primeFactors_mul, Nat.primeFactors_pow,
      Nat.prime_two.primeFactors, Nat.prime_three.primeFactors, Nat.prime_five.primeFactors,
      Nat.prime_seven.primeFactors]
    decide
  simp [hw, Finset.prod_range_succ]

-- At x = 2, the primes dividing 2⁴ - 1 are 3 and 5. Their product gives equality.
example :
    min (1 + 8 * ∏ i ∈ Finset.range (15 : ℕ).primeFactors.card, Nat.nth Nat.Prime i)
        (1 + ∏ i ∈ Finset.range (15 : ℕ).primeFactors.card, Nat.nth Nat.Prime (i + 1)) =
      2 ^ 4 := by
  apply le_antisymm (two_pow_ramified_bound (a := 2) (x := 2) (by decide) (by decide))
  have h15 : (15 : ℕ).primeFactors = {3, 5} := by
    rw [show 15 = 3 * 5 by decide, Nat.primeFactors_mul (by decide) (by decide),
      Nat.prime_three.primeFactors, Nat.prime_five.primeFactors]
    rfl
  simp [h15, Finset.prod_range_succ]

end MetaMathlibExt
