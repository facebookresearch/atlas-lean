/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.TwoNearPerfect

namespace MathlibExtTest.NumberTheory.TwoNearPerfect

-- 352 = 2 ^ 5 * 11 is strongly 2-near perfect with divisor 8.
example : ∃ a ≤ 5, ((11 : ℕ) : ℤ) * (1 + 2 ^ (5 - a)) = 2 ^ (5 + 1) - 2 ^ a - 1 :=
  MetaMathlibExt.strong_two_near_perfect_two_pow_mul_prime_form (k := 5) (p := 11)
    (by decide) (by decide) ⟨8, by decide, by decide⟩

-- The form of the prime gives a divisibility constraint.
example {k : ℕ} (hstrong : ∃ d, d ∣ 2 ^ k * 11 ∧
    ArithmeticFunction.sigma 1 (2 ^ k * 11) = 2 * (2 ^ k * 11) + d + 2 ^ k * 11 / d) :
    ∃ a ≤ k, (1 + (2 : ℤ) ^ (k - a)) ∣ 2 ^ (k + 1) - 2 ^ a - 1 := by
  obtain ⟨a, ha, hform⟩ :=
    MetaMathlibExt.strong_two_near_perfect_two_pow_mul_prime_form (p := 11) (by decide)
      (by decide) hstrong
  exact ⟨a, ha, ((11 : ℕ) : ℤ), hform.symm.trans (by ring)⟩

end MathlibExtTest.NumberTheory.TwoNearPerfect
