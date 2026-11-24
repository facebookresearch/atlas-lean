/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.SuperMZumkeller.TwoPrimes

/-! # Examples with two odd prime factors -/

open MathlibExt.NumberTheory.SuperMZumkellerWanted

-- The least admissible integer has eight divisors.
example : divisorProd 30 = 30 ^ 4 := by decide

example : IsSuperMZumkeller 30 :=
  isSuperMZumkeller_two_pow_mul_two_primes 1 (by decide) 3 5 (by decide) (by decide)
    (by decide) (by decide) (by decide)

-- A larger odd exponent, with the primes supplied in decreasing order.
example : IsSuperMZumkeller 120 :=
  isSuperMZumkeller_two_pow_mul_two_primes 3 (by decide) 5 3 (by decide) (by decide)
    (by decide) (by decide) (by decide)
