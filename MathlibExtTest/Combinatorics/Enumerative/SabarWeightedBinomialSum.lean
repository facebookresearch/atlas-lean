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
  rw [rowSum_add_succ 1 (by decide), rowSum_add_succ 2 (by decide),
    rowSum_add_succ 3 (by decide)]
  decide +kernel
