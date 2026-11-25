/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.SabarWeightedBinomialSum

/-! # Small cases of Sabar's consecutive weighted binomial sums -/

open MetaMathlibExt

private def rowSum (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), (n + k).choose k * 2 ^ k

private theorem rowSum_add_succ (n : ℕ) (hn : 1 ≤ n) :
    rowSum n + rowSum (n + 1) = 3 * 2 ^ n * (2 * n + 2).choose (n + 1) :=
  sum_choose_mul_two_pow_add_succ n hn

-- Independently evaluate the sums at the lower endpoint and the next two rows.
example : rowSum 1 = 5 ∧ rowSum 2 = 31 ∧ rowSum 3 = 209 ∧ rowSum 4 = 1471 := by
  decide +kernel

example : rowSum 1 + rowSum 2 = 36 ∧ rowSum 2 + rowSum 3 = 240 ∧
    rowSum 3 + rowSum 4 = 1680 := by
  decide +kernel

private def alternatingRow (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.Icc 1 n, (-1 : ℚ) ^ (k + 1) *
    (1 - 2 * (k : ℚ) / (n + 1) + (n : ℚ) / (k + 1)) * ((n + k).choose k : ℚ)

-- Use the theorem at the lower endpoint of its published domain.
example : alternatingRow 2 = 2 := sum_neg_one_pow_mul_choose_eq_self 2 (by decide)

-- Independently evaluate the first two rows with opposite parities.
example : alternatingRow 2 = 2 ∧ alternatingRow 3 = 3 := by decide +kernel
