/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum
import MathlibExt.NumberTheory.FibonacciBinomialSum

/-! # Tests for the truncated binomial formula for Fibonacci numbers -/

open MetaMathlibExt

-- At the minimum index, the prefactor and the sole summand are both one.
example : (Nat.fib 2 : ℚ) = 1 := by
  rw [fib_eq_binomial_sum 2 (by decide)]
  norm_num

-- Index four is the first to include a nonzero correction to the power of two.
example : (Nat.fib 4 : ℚ) = 3 := by
  rw [fib_eq_binomial_sum 4 (by decide)]
  norm_num [Finset.sum_range_succ, Ring.choose_one_right]

-- At index seven the sum first includes the term with lower index two.
example : (Nat.fib 7 : ℚ) = 13 := by
  have hchoose : Ring.choose (-1 : ℤ) 2 = 1 := by
    have h := Ring.choose_succ_succ (-1 : ℤ) 1
    norm_num [Ring.choose_one_right, Ring.choose_zero_pos ℤ (by decide : 0 < (2 : ℕ))] at h
    omega
  rw [fib_eq_binomial_sum 7 (by decide)]
  norm_num [Finset.sum_range_succ, Ring.choose_one_right, hchoose]
