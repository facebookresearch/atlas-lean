/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.Complex.ExponentialBounds
import MathlibExt.NumberTheory.ArithmeticFunction.DivisorSummatoryBound

open Finset MetaMathlibExt

-- The bound includes an empty summation interval.
example : ∑ n ∈ Icc 1 (0 : ℕ), (n.divisors.card : ℝ) ≤ 0 := by simp

-- Independently compute the first nontrivial sum, which is 1 + 2 = 3.
example : ∑ n ∈ Icc 1 (2 : ℕ), (n.divisors.card : ℝ) ≤ 2 * (1 + Real.log 2) := by
  rw [show (Icc 1 (2 : ℕ)) = {1, 2} by decide +kernel, sum_insert (by decide), sum_singleton]
  rw [show (1 : ℕ).divisors.card = 1 by decide +kernel,
    show (2 : ℕ).divisors.card = 2 by decide +kernel]
  norm_num
  linarith [Real.log_two_gt_d9]
