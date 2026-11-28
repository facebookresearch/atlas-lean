/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.SpecialFunctions.ArcsinSquareSeries
import Mathlib.Tactic.NormNum

open MetaMathlibExt

-- At the origin both the individual terms and the proposed sum vanish.
example :
    HasSum (fun n : ℕ =>
      ((4 : ℝ) ^ n / (((n + 1).centralBinom : ℝ) * ((n : ℝ) + 1) ^ 2)) * (0 : ℝ) ^ (2 * n + 2))
      (Real.arcsin 0 ^ 2 / 2) := by
  simp

-- At a negative input, the first two terms are positive and have the expected coefficients.
example :
    ∑ n ∈ Finset.range 2,
      ((4 : ℝ) ^ n / (((n + 1).centralBinom : ℝ) * ((n : ℝ) + 1) ^ 2)) * (-1 / 2) ^ (2 * n + 2) =
      13 / 96 := by
  norm_num [Finset.sum_range_succ, Nat.centralBinom, Nat.choose]

example :
    HasSum (fun n : ℕ =>
      ((4 : ℝ) ^ n / (((n + 1).centralBinom : ℝ) * ((n : ℝ) + 1) ^ 2)) * (-1 / 2) ^ (2 * n + 2))
      (Real.arcsin (-1 / 2) ^ 2 / 2) :=
  hasSum_arcsin_sq_div_two (by norm_num)
