/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum.Prime
import MathlibExt.NumberTheory.PrimePairPowAddTwoPowEvenMulPowEqSq

/-! # Tests for the square classification for scaled prime pairs -/

open MetaMathlibExt

-- The `y = 0` solution holds for every allowed scaling exponent.
example (k : ℕ) (hk : 1 ≤ k) : 3 ^ 1 + (2 ^ (2 * k) * (2 * 3 - 1)) ^ 0 = (2 : ℕ) ^ 2 :=
  (prime_pair_pow_add_two_pow_even_mul_pow_eq_sq_iff (by decide) (by decide) (by decide) hk
    1 0 2).2 (Or.inl rfl)

-- At `x = 0`, the other solution occurs at `k = 2`.
example : (3 : ℕ) ^ 0 + (2 ^ (2 * 2) * 5) ^ 1 = 9 ^ 2 :=
  (prime_pair_pow_add_two_pow_even_mul_pow_eq_sq_iff (by decide) (by decide) (by decide)
    (by decide : 1 ≤ 2) 0 1 9).2 (Or.inr rfl)

-- At the minimum scaling exponent, the `x = 0` solution is absent.
example (y z : ℕ) : 1 + 20 ^ y ≠ z ^ 2 := by
  intro h
  have hsol := (prime_pair_pow_add_two_pow_even_mul_pow_eq_sq_iff (p := 3) (k := 1)
    (by decide) (by decide) (by decide) (by decide) 0 y z).1 (by simpa using h)
  simp at hsol

-- Positive exponents give neither of the two solutions even for the pair `(3, 5)`.
example (k x y z : ℕ) (hk : 1 ≤ k) (hx : 0 < x) (hy : 0 < y) :
    (3 : ℕ) ^ x + (2 ^ (2 * k) * 5) ^ y ≠ z ^ 2 := by
  intro h
  have hsol := (prime_pair_pow_add_two_pow_even_mul_pow_eq_sq_iff (p := 3) (by decide)
    (by decide) (by decide) hk x y z).1 h
  simp [Prod.mk.injEq, hx.ne', hy.ne'] at hsol

-- A different prime pair has no solutions, including at the zero exponents.
example (k x y z : ℕ) (hk : 1 ≤ k) :
    (19 : ℕ) ^ x + (2 ^ (2 * k) * 37) ^ y ≠ z ^ 2 := by
  intro h
  have hsol := (prime_pair_pow_add_two_pow_even_mul_pow_eq_sq_iff (p := 19) (by norm_num)
    (by norm_num) (by decide) hk x y z).1 h
  simp at hsol
