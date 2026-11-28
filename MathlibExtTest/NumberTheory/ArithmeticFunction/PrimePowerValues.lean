/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ArithmeticFunction.PrimePowerValues

open ArithmeticFunction

private def coefficient (p e : ℕ) : ℕ := p + e

-- The coefficients at exponent zero do not affect either boundary value.
example : ofPrimePowerValues coefficient 0 = 0 := by simp

example : ofPrimePowerValues coefficient 1 = 1 :=
  (isMultiplicative_ofPrimePowerValues coefficient).map_one

-- The values at 2² and 3² differ despite the equal exponents.
example : ofPrimePowerValues coefficient (2 ^ 2) = 4 :=
  ofPrimePowerValues_prime_pow coefficient Nat.prime_two (by decide)

example : ofPrimePowerValues coefficient (3 ^ 2) = 5 :=
  ofPrimePowerValues_prime_pow coefficient Nat.prime_three (by decide)

-- A mixed factorization uses both the prime and the exponent of each factor.
example : ofPrimePowerValues coefficient 45 = 30 := by
  change ofPrimePowerValues coefficient (3 ^ 2 * 5 ^ 1) = 30
  rw [(isMultiplicative_ofPrimePowerValues coefficient).map_mul_of_coprime (by decide),
    ofPrimePowerValues_prime_pow coefficient Nat.prime_three (by decide),
    ofPrimePowerValues_prime_pow coefficient (show Nat.Prime 5 by decide) (by decide)]
  decide
