/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.PrimePairOneAddTwoPowMulPowEqSq

/-! # Tests for squares one more than a power of `2 ^ k * (2 * p - 1)` -/

open MetaMathlibExt

example : 1 + (2 ^ 4 * (2 * 3 - 1)) ^ 1 = (9 : ℕ) ^ 2 :=
  (one_add_two_pow_mul_pow_eq_sq_iff (p := 3) (by decide) (by decide) (by decide)
    (by decide) 1 9).2 rfl

-- The exponent zero gives no solution, even for the prime pair that admits a square.
example (k z : ℕ) (hk : 1 ≤ k) : 1 + (2 ^ k * (2 * 3 - 1)) ^ 0 ≠ z ^ 2 := by
  intro h
  have := (one_add_two_pow_mul_pow_eq_sq_iff (p := 3) (by decide) (by decide) (by decide)
    hk 0 z).1 h
  simp at this

-- The prime pair (7, 13) admits no solution for any positive k.
example (k y z : ℕ) (hk : 1 ≤ k) : 1 + (2 ^ k * 13) ^ y ≠ z ^ 2 := by
  intro h
  have := (one_add_two_pow_mul_pow_eq_sq_iff (p := 7) (by decide) (by decide) (by decide)
    hk y z).1 h
  simp at this

-- Allowing the even prime would also give 1 + 8 * 3 = 25.
example : 1 + (2 ^ 3 * (2 * 2 - 1)) ^ 1 = (5 : ℕ) ^ 2 := rfl
