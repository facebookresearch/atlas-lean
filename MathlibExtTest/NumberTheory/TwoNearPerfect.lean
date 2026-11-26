/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.TwoNearPerfect

/-!
# Specializations of the omitted-divisor obstruction for two-near perfect numbers
-/

namespace MathlibExtTest.NumberTheory.TwoNearPerfect

example {i : ℕ} (hi : i ≤ 2) :
    ArithmeticFunction.sigma 1 36 ≠ 2 * 36 + 2 ^ i + 3 := by
  simpa using MetaMathlibExt.not_two_near_perfect_two_pow_mul_prime_sq_case_two
    (k := 2) (p := 3) (m := 1) Nat.prime_three (by decide) hi (Or.inl rfl)

example : ArithmeticFunction.sigma 1 9 ≠ 2 * 9 + 1 + 9 := by
  simpa using MetaMathlibExt.not_two_near_perfect_two_pow_mul_prime_sq_case_two
    (k := 0) (p := 3) (i := 0) (m := 2) Nat.prime_three (by decide) (by decide) (Or.inr rfl)

end MathlibExtTest.NumberTheory.TwoNearPerfect
