/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.SuperMZumkellerFactorization
import MathlibExt.NumberTheory.SuperMZumkellerTwoPowMulProdPrimes

open MathlibExt.NumberTheory.SuperMZumkellerWanted

private def oddPrimes : Finset ℕ := {3, 5, 7}

-- At k = 0 the product is 105. Check its exact divisor count and the criterion directly.
example : IsSuperMZumkeller ((2 : ℕ) ^ 0 * ∏ p ∈ oddPrimes, p) := by
  rw [show (2 : ℕ) ^ 0 * ∏ p ∈ oddPrimes, p = 105 by decide]
  have hcard : (105 : ℕ).divisors.card = 8 := by decide
  refine (isSuperMZumkeller_iff 105 (by decide)).2 fun p _ ↦ ?_
  rw [hcard]
  exact dvd_mul_of_dvd_left (dvd_mul_left 8 _) _

-- At k = 1 the product is 210, with twice as many divisors.
example : IsSuperMZumkeller ((2 : ℕ) ^ 1 * ∏ p ∈ oddPrimes, p) := by
  rw [show (2 : ℕ) ^ 1 * ∏ p ∈ oddPrimes, p = 210 by decide]
  have hcard : (210 : ℕ).divisors.card = 16 := by decide
  refine (isSuperMZumkeller_iff 210 (by decide)).2 fun p _ ↦ ?_
  rw [hcard]
  exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (by decide : 8 ∣ 16) _) _

-- The new API applies to the same prime set at every natural exponent.
example (k : ℕ) : IsSuperMZumkeller ((2 : ℕ) ^ k * ∏ p ∈ oddPrimes, p) :=
  isSuperMZumkeller_two_pow_mul_prod_primes k oddPrimes (by decide) (by decide) (by decide)
