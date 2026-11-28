/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.CentralBinomSeriesSpecialValues
import Mathlib.Tactic.NormNum

open MetaMathlibExt

-- Independently check the first two endpoint terms, including the index shift in the binomial.
example :
    ∑ n ∈ Finset.range 2, (4 : ℝ) ^ n / (((n + 1).centralBinom : ℝ) * ((n : ℝ) + 1) ^ 2) =
      2 / 3 := by
  norm_num [Finset.sum_range_succ, Nat.centralBinom, Nat.choose]

-- The telescoping comparison is sharp at the first endpoint coefficient.
example :
    (1 : ℝ) / (((1 : ℕ).centralBinom : ℝ) * 1 ^ 2) =
      3 * (1 / ((1 : ℕ).centralBinom : ℝ) - 4 / (2 * ((2 : ℕ).centralBinom : ℝ))) := by
  norm_num [Nat.centralBinom, Nat.choose]

-- Independently check the first two harmonic pairs and the next even/odd pair.
example :
    ∑ n ∈ Finset.range 2, 1 / ((2 * (n : ℝ) + 1) * ((n : ℝ) + 1)) = (7 : ℝ) / 6 := by
  norm_num [Finset.sum_range_succ]

example :
    (1 : ℝ) / (5 * 3) = 2 * (((-1 : ℝ) ^ 4) / 5 + ((-1 : ℝ) ^ 5) / 6) := by
  norm_num

-- Check that clients can use the original declaration and access both values by projection.
example :
    (∑' n : ℕ, (4 : ℝ) ^ n / (((n + 1).centralBinom : ℝ) * ((n : ℝ) + 1) ^ 2)) +
      (∑' n : ℕ, 1 / ((2 * (n : ℝ) + 1) * ((n : ℝ) + 1))) =
        Real.pi ^ 2 / 8 + 2 * Real.log 2 :=
  congrArg₂ (· + ·) tsum_four_pow_div_centralBinom_mul_sq_special.1
    tsum_four_pow_div_centralBinom_mul_sq_special.2
