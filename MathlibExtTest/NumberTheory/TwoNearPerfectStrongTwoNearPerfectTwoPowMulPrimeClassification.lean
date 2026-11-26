/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.TwoNearPerfectStrongTwoNearPerfectTwoPowMulPrimeClassification

namespace MathlibExtTest.NumberTheory.TwoNearPerfectStrongTwoNearPerfectTwoPowMulPrimeClassification

-- With `a = 3`, `k = 5` and `p = 11`, the equation `p * (1 + 2 ^ (k - a)) = 55` holds.
example : 5 = 3 + 2 ∧ 2 ^ 5 * 11 / 2 ^ 3 = 4 * 11 ∧ (5 * 11 : ℤ) = 2 ^ (3 + 3) - 2 ^ 3 - 1 ∧
    3 % 4 = 3 :=
  MetaMathlibExt.strong_two_near_perfect_two_pow_mul_prime_classification
    (by decide) (by decide) (by decide)

-- The congruence `a ≡ 3 (mod 4)` on the same instance.
example : (3 : ℕ) % 4 = 3 :=
  (MetaMathlibExt.strong_two_near_perfect_two_pow_mul_prime_classification (a := 3) (k := 5)
    (p := 11) (by decide) (by decide) (by decide)).2.2.2

end MathlibExtTest.NumberTheory.TwoNearPerfectStrongTwoNearPerfectTwoPowMulPrimeClassification
