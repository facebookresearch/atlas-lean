/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ArithmeticFunction.PrimitiveNondeficientTwoPowMulPrime

open MathlibExt.NumberTheory.PrimitiveNondeficientWanted

-- At exponent zero the number is the prime itself.
example {p : ℕ} (hp : p.Prime) (hpo : p ≠ 2) : ¬ IsPrimitiveNondeficient p := by
  simpa [hp.one_lt, hp.one_lt.not_ge] using
    (isPrimitiveNondeficient_two_pow_mul_prime_iff 0 p hp hpo)

-- Both the abundant number 20 and the perfect number 28 lie in the interval for exponent two.
example : IsPrimitiveNondeficient 20 :=
  (isPrimitiveNondeficient_two_pow_mul_prime_iff 2 5 (by decide) (by decide)).mpr (by decide)

example : IsPrimitiveNondeficient 28 :=
  (isPrimitiveNondeficient_two_pow_mul_prime_iff 2 7 (by decide) (by decide)).mpr (by decide)

-- The primes 3 and 11 fall on opposite sides of that interval.
example : ¬ IsPrimitiveNondeficient 12 :=
  mt (isPrimitiveNondeficient_two_pow_mul_prime_iff 2 3 (by decide) (by decide)).mp (by decide)

example : ¬ IsPrimitiveNondeficient 44 :=
  mt (isPrimitiveNondeficient_two_pow_mul_prime_iff 2 11 (by decide) (by decide)).mp (by decide)
