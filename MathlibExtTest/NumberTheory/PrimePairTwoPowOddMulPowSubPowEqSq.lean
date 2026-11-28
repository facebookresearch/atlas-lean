/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.Prime
import MathlibExt.NumberTheory.PrimePairTwoPowOddMulPowSubPowEqSq

/-! # Tests for squares of the form `(2 ^ (2 * k + 1) * (2 * p - 1)) ^ x - p ^ y` -/

open MetaMathlibExt

/-! The trivial solution, for the prime pair `(37, 73)` and every `k`. -/

example (k : ℕ) :
    ((2 : ℤ) ^ (2 * k + 1) * (2 * ((37 : ℕ) : ℤ) - 1)) ^ 0 - ((37 : ℕ) : ℤ) ^ 0 =
      ((0 : ℕ) : ℤ) ^ 2 :=
  (prime_pair_two_pow_odd_mul_pow_sub_pow_eq_sq_iff (p := 37) (by norm_num) (by norm_num)
    (by decide) k 0 0 0).2 (Or.inl rfl)

/-! The second family: for the prime pair `(157, 313)` we have `4 * 157 = 25 ^ 2 + 3`, so
`2 * 313 - 1 = 25 ^ 2`. -/

example : ((2 : ℤ) ^ (2 * 0 + 1) * (2 * ((157 : ℕ) : ℤ) - 1)) ^ 1 - ((157 : ℕ) : ℤ) ^ 0 =
    ((25 : ℕ) : ℤ) ^ 2 :=
  (prime_pair_two_pow_odd_mul_pow_sub_pow_eq_sq_iff (p := 157) (by norm_num) (by norm_num)
    (by decide) 0 1 0 25).2 (Or.inr ⟨rfl, rfl, rfl, rfl⟩)

/-! For the prime pair `(37, 73)` and `k = 0`, `146 ^ x - 37 ^ y` is a square only for
`x = y = 0`, because `4 * 37 - 3 = 145` is not a square. -/

example (x y z : ℕ) (h : (146 : ℤ) ^ x - 37 ^ y = (z : ℤ) ^ 2) : x = 0 ∧ y = 0 ∧ z = 0 := by
  have sol := (prime_pair_two_pow_odd_mul_pow_sub_pow_eq_sq_iff (p := 37) (by norm_num)
    (by norm_num) (by decide) 0 x y z).1 (by norm_num [h])
  simp only [Prod.mk.injEq] at sol
  rcases sol with sol | ⟨h145, -, -, -⟩
  · exact sol
  · have hz : z < 13 := by nlinarith
    interval_cases z <;> omega

/-! For `k ≥ 1` only the trivial solution remains: for the prime pair `(37, 73)` and `k = 1`,
`584 ^ x - 37 ^ y` is never a square once `x ≥ 1`. -/

example (x y z : ℕ) (hx : 0 < x) : (584 : ℤ) ^ x - 37 ^ y ≠ (z : ℤ) ^ 2 := by
  intro h
  have sol := (prime_pair_two_pow_odd_mul_pow_sub_pow_eq_sq_iff (p := 37) (by norm_num)
    (by norm_num) (by decide) 1 x y z).1 (by norm_num [h])
  simp only [Prod.mk.injEq] at sol
  omega

/-! The congruence `p % 8 = 5` cannot be weakened to `p % 4 = 1`: for the prime pair
`(97, 193)`, where `97 % 8 = 1`, the triple `(x, y, z) = (1, 1, 17)` is a solution with `k = 0`,
since `386 - 97 = 17 ^ 2`. -/

example : (97 : ℕ).Prime ∧ (2 * 97 - 1 : ℕ).Prime ∧ 97 % 8 = 1 ∧
    ((2 : ℤ) ^ (2 * 0 + 1) * (2 * ((97 : ℕ) : ℤ) - 1)) ^ 1 - ((97 : ℕ) : ℤ) ^ 1 =
      ((17 : ℕ) : ℤ) ^ 2 := by
  norm_num

/-! For the prime pair `(3, 5)`, where `3 % 8 = 3`, the triple `(x, y, z) = (1, 2, 1)` is a
solution with `k = 0`, since `10 - 3 ^ 2 = 1 ^ 2`. -/

example : (3 : ℕ).Prime ∧ (2 * 3 - 1 : ℕ).Prime ∧ 3 % 8 = 3 ∧
    ((2 : ℤ) ^ (2 * 0 + 1) * (2 * ((3 : ℕ) : ℤ) - 1)) ^ 1 - ((3 : ℕ) : ℤ) ^ 2 =
      ((1 : ℕ) : ℤ) ^ 2 := by
  norm_num
