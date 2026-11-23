/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.DivisorCountBound

-- Zero has an empty divisor finset.
example : ((0 : ℕ).divisors.card : ℝ) ≤ 0 := by
  simpa only [Nat.cast_zero, Real.sqrt_zero, mul_zero] using
    MetaMathlibExt.card_divisors_le_two_mul_sqrt 0

-- For a perfect square the square root is its own complementary divisor.
example (k : ℕ) : (k ^ 2).divisors.card ≤ 2 * k := by
  have h := MetaMathlibExt.card_divisors_le_two_mul_sqrt (k ^ 2)
  rw [Nat.cast_pow, Real.sqrt_sq (Nat.cast_nonneg k)] at h
  exact_mod_cast h
