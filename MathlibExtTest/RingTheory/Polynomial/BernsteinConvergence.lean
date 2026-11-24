/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.RingTheory.Polynomial.BernsteinConvergence
import Mathlib.Tactic.NormNum

open bernsteinPolynomial

-- The coefficient is zero when the grid index is smaller than the power degree.
example : |((1 : ℕ).choose 3 : ℝ) / (8 : ℕ).choose 3 - (1/8 : ℝ)^3| ≤ 9/8 := by
  convert abs_choose_ratio_sub_pow_le (n := 8) (k := 1) (d := 3)
    (by norm_num) (by norm_num) (by norm_num) using 1
  all_goals norm_num [Nat.choose]

-- Exact independent error for a quadratic at a non-endpoint index.
example : |((2 : ℕ).choose 2 : ℝ) / (4 : ℕ).choose 2 - (2/4 : ℝ)^2| = 1/12 := by
  norm_num [Nat.choose]

example : |((2 : ℕ).choose 2 : ℝ) / (4 : ℕ).choose 2 - (2/4 : ℝ)^2| ≤ 1 := by
  convert abs_choose_ratio_sub_pow_le (n := 4) (k := 2) (d := 2)
    (by norm_num) (by norm_num) (by norm_num) using 1
  norm_num [Nat.choose]

-- Degree zero and endpoint indices are included uniformly, not by separate APIs.
example (n k : ℕ) (hn : 0 < n) (hk : k ≤ n) :
    |(k.choose 0 : ℝ) / n.choose 0 - ((k : ℝ) / n)^0| ≤ 0 := by
  have h := abs_choose_ratio_sub_pow_le (d := 0) hn hk (Nat.zero_le n)
  simpa only [Nat.cast_zero, zero_pow (by decide : 2 ≠ 0), zero_div] using h

example (n d : ℕ) (hn : 0 < n) (hd : 2*d ≤ n) :
    |(n.choose d : ℝ) / n.choose d - ((n : ℝ) / n)^d| ≤ (d : ℝ)^2/n :=
  abs_choose_ratio_sub_pow_le hn le_rfl hd

example (n d : ℕ) (hn : 0 < n) (hd : 2*d ≤ n) :
    |((0 : ℕ).choose d : ℝ) / n.choose d - ((0 : ℝ) / n)^d| ≤ (d : ℝ)^2/n := by
  simpa only [Nat.cast_zero] using abs_choose_ratio_sub_pow_le hn (Nat.zero_le _) hd

-- Independent finite-product regression includes zero factors.
example : |((0 : ℝ) * (3/4)) - (1/2) * 1| ≤ |0 - (1/2 : ℝ)| + |3/4 - (1 : ℝ)| := by
  norm_num

#print axioms Finset.abs_prod_sub_prod_le_sum_of_mem_Icc
#print axioms abs_choose_ratio_sub_pow_le
