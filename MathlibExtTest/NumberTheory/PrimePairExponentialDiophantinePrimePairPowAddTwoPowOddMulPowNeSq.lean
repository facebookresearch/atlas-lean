/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.PrimePairExponentialDiophantinePrimePairPowAddTwoPowOddMulPowNeSq

/-! # Tests for no squares of the form `p ^ x + (2 ^ (2 * k + 1) * (2 * p - 1)) ^ y` -/

namespace MathlibExtTest.NumberTheory.PrimePairExponentialDiophantinePrimePairPowAddTwoPowOddMulPowNeSq

open MetaMathlibExt

-- The prime pair `(7, 13)` admits no solution for any exponents.
example (k x y z : ℕ) : 7 ^ x + (2 ^ (2 * k + 1) * 13) ^ y ≠ z ^ 2 := by
  have h := prime_pair_pow_add_two_pow_odd_mul_pow_ne_sq (p := 7) (by decide)
    (by decide) (Or.inr rfl) k x y z
  simpa using h

-- A concrete instance: `7 + 26 = 33` is not a square.
example : 7 ^ 1 + (2 ^ (2 * 0 + 1) * (2 * 7 - 1)) ^ 1 ≠ (5 : ℕ) ^ 2 :=
  prime_pair_pow_add_two_pow_odd_mul_pow_ne_sq (by decide) (by decide) (Or.inr rfl)
    0 1 1 5

end MathlibExtTest.NumberTheory.PrimePairExponentialDiophantinePrimePairPowAddTwoPowOddMulPowNeSq
