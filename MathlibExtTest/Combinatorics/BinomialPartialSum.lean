/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Combinatorics.BinomialPartialSum
import Mathlib.Tactic.NormNum

open Finset

example : (∑ j ∈ range 3, (Nat.choose 5 j : ℝ)) = 16 := by
  norm_num [sum_range_succ, Nat.choose]

example : (∑ j ∈ range 3, (Nat.choose 5 j : ℝ)) ≤ (3 * 5 / 2 : ℝ) ^ 2 := by
  exact Real.sum_choose_le_pow (by norm_num) (by norm_num)

example : (1 / 2 : ℝ) ^ 2 * ∑ j ∈ range 3, (Nat.choose 5 j : ℝ) ≤
    Real.exp (5 * (1 / 2 : ℝ)) := by
  exact Real.pow_mul_sum_choose_le_exp (D := 5) (r := 2) (x := 1 / 2)
    (by norm_num) (by norm_num) (by norm_num)

-- r = D, x = 1: the weighted polynomial bound is attained.
example : (1 : ℝ) ^ 5 * ∑ j ∈ range 6, (Nat.choose 5 j : ℝ) ≤ (1 + 1 : ℝ) ^ 5 := by
  exact Real.pow_mul_sum_choose_le (by norm_num) (by norm_num) (by norm_num)

-- Empty ambient set and r = 0, including Lean's 0^0 = 1 convention.
example : (0 : ℝ) ^ 0 * ∑ j ∈ range 1, (Nat.choose 0 j : ℝ) ≤ (0 + 1 : ℝ) ^ 0 := by
  exact Real.pow_mul_sum_choose_le (by norm_num) (by norm_num) (by norm_num)

example : (0 : ℝ) ^ 0 * ∑ j ∈ range 1, (Nat.choose 0 j : ℝ) ≤ Real.exp (0 * (0 : ℝ)) := by
  simpa only [Nat.cast_zero] using Real.pow_mul_sum_choose_le_exp (D := 0) (r := 0) (x := 0)
    (by norm_num) (by norm_num) (by norm_num)

example : (∑ j ∈ range 2, (Nat.choose 1 j : ℝ)) ≤ (3 * 1 / 1 : ℝ) ^ 1 := by
  simpa only [Nat.cast_one] using
    Real.sum_choose_le_pow (D := 1) (r := 1) (by norm_num) (by norm_num)

#print axioms Real.pow_mul_sum_choose_le
#print axioms Real.pow_mul_sum_choose_le_exp
#print axioms Real.sum_choose_le_pow
