/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum.Prime
import MathlibExt.NumberTheory.PrimePairPowSubTwoPowOddMulPowEqSq

open MetaMathlibExt

/-! The trivial solution, for the prime pair `(3, 5)` and every `k`. -/

example (k : ℕ) :
    ((3 : ℕ) : ℤ) ^ 0 - ((2 : ℤ) ^ (2 * k + 1) * (2 * ((3 : ℕ) : ℤ) - 1)) ^ 0 = ((0 : ℕ) : ℤ) ^ 2 :=
  (prime_pair_pow_sub_two_pow_odd_mul_pow_eq_sq_iff (by decide) (by decide) (by decide)
    k 0 0 0).2 rfl

/-! For the prime pair `(3, 5)` and `k = 0`, `3 ^ x - 10 ^ y` is a square only for `x = y = 0`. -/

example (x y z : ℕ) (h : (3 : ℤ) ^ x - 10 ^ y = (z : ℤ) ^ 2) : x = 0 ∧ y = 0 ∧ z = 0 := by
  have sol := (prime_pair_pow_sub_two_pow_odd_mul_pow_eq_sq_iff (p := 3) (by decide) (by decide)
    (by decide) 0 x y z).1 (by norm_num [h])
  simpa only [Prod.mk.injEq] using sol

/-! For the prime pair `(19, 37)` and `k = 1`, no positive power of `19` exceeds a power of
`2 ^ 3 * 37 = 296` by a square. -/

example (x y z : ℕ) (hx : 0 < x) : (19 : ℤ) ^ x - 296 ^ y ≠ (z : ℤ) ^ 2 := by
  intro h
  have sol := (prime_pair_pow_sub_two_pow_odd_mul_pow_eq_sq_iff (p := 19) (by decide) (by decide)
    (by decide) 1 x y z).1 (by norm_num [h])
  simp only [Prod.mk.injEq] at sol
  omega

/-! The case `y = 0`: for the prime pair `(139, 277)`, `139 ^ x - 1` is not a square when
`x ≥ 1`. -/

example (x z : ℕ) (hx : 0 < x) : (139 : ℤ) ^ x - 1 ≠ (z : ℤ) ^ 2 := by
  intro h
  have sol := (prime_pair_pow_sub_two_pow_odd_mul_pow_eq_sq_iff (p := 139) (by norm_num)
    (by norm_num) (by decide) 0 x 0 z).1 (by norm_num [h])
  simp only [Prod.mk.injEq] at sol
  omega

/-! The congruence `p % 8 = 3` cannot be dropped: for the prime pair `(37, 73)`, where
`37 % 8 = 5`, the triple `(x, y, z) = (1, 0, 6)` is a solution. -/

example : (37 : ℕ).Prime ∧ (2 * 37 - 1 : ℕ).Prime ∧ 37 % 8 = 5 ∧
    ((37 : ℕ) : ℤ) ^ 1 - ((2 : ℤ) ^ (2 * 0 + 1) * (2 * ((37 : ℕ) : ℤ) - 1)) ^ 0 =
      ((6 : ℕ) : ℤ) ^ 2 := by
  norm_num
