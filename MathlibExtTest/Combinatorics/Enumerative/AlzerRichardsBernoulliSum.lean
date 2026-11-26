/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.AlzerRichardsBernoulliSum
import Mathlib.Tactic.NormNum

open Finset MetaMathlibExt

-- The constant coefficient is 1 for every truncation, including n = 0.
example (n : ℕ) :
    ∑ k ∈ range (n + 1), (-1 : ℚ) ^ k * (n + 1).choose (k + 1) = 1 := by
  simpa [Nat.stirlingSecond_self] using
    (sum_choose_div_choose_mul_stirlingSecond_eq_bernoulli n).1 0 (Nat.zero_le n)

-- With n = 2 the interior value at r = 1 uses the negative Bernoulli convention.
example :
    ∑ k ∈ range 3, (-1 : ℚ) ^ k * ((Nat.choose 3 (k + 1) : ℚ) / ((1 + k).choose k : ℚ)) *
        (Nat.stirlingSecond (1 + k) k : ℚ) = -1 / 2 := by
  simpa only [bernoulli_one] using
    (sum_choose_div_choose_mul_stirlingSecond_eq_bernoulli 2).1 1 (by decide)

-- At r = 3 the Bernoulli number vanishes and the entire sum is the boundary correction.
example :
    ∑ k ∈ range 3, (-1 : ℚ) ^ k * ((Nat.choose 3 (k + 1) : ℚ) / ((3 + k).choose k : ℚ)) *
        (Nat.stirlingSecond (3 + k) k : ℚ) = 3 / 4 := by
  have h := (sum_choose_div_choose_mul_stirlingSecond_eq_bernoulli 2).2
  rw [bernoulli_eq_zero_of_odd (by decide) (by decide)] at h
  convert h using 1
  norm_num [Nat.factorial]
