/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.TwoNearPerfectPowerOfTwoDivisors

namespace MetaMathlibExt

-- Both orders of the omitted divisors satisfy the hypothesis at 18.
example {i j : ℕ} (h : (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0)) :
    ArithmeticFunction.sigma 1 18 = 2 * 18 + 2 ^ i + 2 ^ j := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

-- At 36 the omitted divisors cannot both be powers of two.
example {i j : ℕ} (hi : i ≤ 2) (hj : j ≤ 2) (hij : i ≠ j) :
    ArithmeticFunction.sigma 1 36 ≠ 2 * 36 + 2 ^ i + 2 ^ j := by
  intro h
  have hnum := (two_near_perfect_two_pow_mul_prime_sq_case_one (k := 2) Nat.prime_three
    (by decide) hi hj hij h).1
  exact (by decide : 2 ^ 2 * 3 ^ 2 ≠ 18) hnum

end MetaMathlibExt
