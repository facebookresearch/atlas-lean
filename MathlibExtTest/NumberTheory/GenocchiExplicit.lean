/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.GenocchiExplicit
import Mathlib.Tactic.NormNum

open MathlibExt.NumberTheory.GenocchiExplicitWanted

-- At k = j = 0 the factorial argument truncates to zero.
example : zerroU 0 0 = 1 := by
  norm_num [zerroU]

-- The first step at the smallest admissible k uses the row r = 0.
example : zerroU 1 1 = -1 / 2 := by
  rw [zerroU_succ 0 1 (by decide)]
  norm_num [zerroU]

-- In this step both terms contribute, and the second has multiplicity two.
example : zerroU 3 2 = -1 / 4 := by
  rw [zerroU_succ 2 2 (by decide)]
  norm_num [zerroU, Finset.sum_range_succ, Nat.factorial, Nat.stirlingSecond]

-- At n = r + 1 the outer sum consists only of the zeroth difference of the constant one.
example : (-1 : ℚ) ^ 2 * bernoulli 2 = 1 / 6 := by
  rw [neg_one_pow_mul_bernoulli_eq_sum_one 2 1 (by decide) (by decide) (by decide)]
  norm_num [Finset.sum_range_succ, diffPowEval, Nat.factorial, Nat.stirlingSecond]

-- For n = 4 and r = 1 the differences of the square at one have orders zero, one and two.
example : (-1 : ℚ) ^ 4 * bernoulli 4 = -1 / 30 := by
  rw [neg_one_pow_mul_bernoulli_eq_sum_one 4 1 (by decide) (by decide) (by decide)]
  norm_num [Finset.sum_range_succ, diffPowEval, Function.iterate_succ_apply,
    Nat.factorial, Nat.stirlingSecond]

-- At n = r + 1 the outer sum is the single first difference of the identity at zero.
example : (-1 : ℚ) ^ 2 * bernoulli 2 = 1 / 6 := by
  rw [neg_one_pow_mul_bernoulli_eq_sum_zero 2 1 (by decide) (by decide) (by decide)]
  norm_num [Finset.sum_range_succ, diffPowEval, Nat.factorial, Nat.stirlingSecond]

-- For n = 4 and r = 1 the differences of the cube at zero have orders one, two and three.
example : (-1 : ℚ) ^ 4 * bernoulli 4 = -1 / 30 := by
  rw [neg_one_pow_mul_bernoulli_eq_sum_zero 4 1 (by decide) (by decide) (by decide)]
  norm_num [Finset.sum_Icc_succ_top, Finset.sum_range_succ, diffPowEval,
    Function.iterate_succ_apply, Nat.factorial, Nat.stirlingSecond]

-- For n = 4 and r = 2 the weight of the first difference vanishes.
example : (-1 : ℚ) ^ 4 * bernoulli 4 = -1 / 30 := by
  rw [neg_one_pow_mul_bernoulli_eq_sum_zero 4 2 (by decide) (by decide) (by decide)]
  norm_num [Finset.sum_Icc_succ_top, Finset.sum_range_succ, diffPowEval,
    Function.iterate_succ_apply, Nat.factorial, Nat.stirlingSecond]

-- At n = r + 1 the sum for H_{n,r} has only its k = 1 term.
example : zerroH 3 1 = -3 / 4 := by
  rw [← zerroH_eq 3 2 (by decide) (by decide)]
  norm_num [zerroH, zerroU, Finset.sum_Icc_succ_top, Finset.sum_range_succ,
    Nat.factorial, Nat.stirlingSecond]

-- At r = 1 the step reaches H_{n,0}; the row for H_{n,1} has several terms.
example : zerroH 5 0 = 5 / 2 := by
  rw [← zerroH_eq 5 1 (by decide) (by decide)]
  norm_num [zerroH, zerroU, Finset.sum_Icc_succ_top, Finset.sum_range_succ,
    Nat.factorial, Nat.stirlingSecond]
