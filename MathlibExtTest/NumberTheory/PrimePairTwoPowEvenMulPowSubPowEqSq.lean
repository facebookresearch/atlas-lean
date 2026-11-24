/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.PrimePairTwoPowEvenMulPowSubPowEqSq

/-! # Boundary cases for the prime-pair square classification -/

open MetaMathlibExt

-- The zero triple works for the smallest prime pair and every positive k.
example (k : ℕ) (hk : 1 ≤ k) :
    ((2 : ℤ) ^ (2 * k) * 5) ^ 0 - 3 ^ 0 = 0 ^ 2 :=
  (prime_pair_two_pow_even_mul_pow_sub_pow_eq_sq_iff (p := 3) (by decide) (by decide)
    (by decide) hk 0 0 0).2 rfl

-- At k = 1, even a single positive exponent rules out a square for the pair (7, 13).
example (x y z : ℕ) (hpos : 0 < x ∨ 0 < y) : (52 : ℤ) ^ x - 7 ^ y ≠ (z : ℤ) ^ 2 := by
  intro h
  have hzero := (prime_pair_two_pow_even_mul_pow_sub_pow_eq_sq_iff (p := 7) (k := 1)
    (by decide) (by decide) (by decide) (by decide) x y z).1 h
  simp only [Prod.mk.injEq] at hzero
  omega

-- With k = 0 the pair (3, 5) admits the nonzero solution (1, 0, 2).
example : ((2 : ℤ) ^ (2 * 0) * (2 * 3 - 1)) ^ 1 - 3 ^ 0 = 2 ^ 2 := by decide
