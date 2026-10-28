/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.PrimeCounting.Mertens

/-!
# Tests for Mertens' first theorem
-/

@[expose] public section

open Finset ArithmeticFunction Chebyshev

-- `log 3! = Λ(2) + Λ(3)` (the terms `d = 2, 3` each with `⌊3 / d⌋ = 1`).
example : Real.log (Nat.factorial 3 : ℝ) =
    ∑ d ∈ Ioc 0 3, vonMangoldt d * ((3 / d : ℕ) : ℝ) :=
  log_factorial_eq_sum_vonMangoldt_mul_div 3

example : Real.log (Nat.factorial 0 : ℝ) = ∑ d ∈ Ioc 0 0, vonMangoldt d * ((0 / d : ℕ) : ℝ) := by
  simp

-- Boundary `x = 1`: `|0 - 0| ≤ log 4 + 6`.
example : |∑ n ∈ Ioc 0 ⌊(1 : ℝ)⌋₊, vonMangoldt n / (n : ℝ) - Real.log 1| ≤ Real.log 4 + 6 :=
  abs_sum_vonMangoldt_div_sub_log_le 1 le_rfl

example : ∑ p ∈ Nat.primesLE 1, Real.log p / (p : ℝ) ≤ Real.log ((1 : ℕ) : ℝ) + (Real.log 4 + 6) :=
  sum_primesLE_log_div_le 1 le_rfl

example : (fun x : ℝ => ∑ n ∈ Ioc 0 ⌊x⌋₊, vonMangoldt n / (n : ℝ) - Real.log x)
    =O[Filter.atTop] fun _ : ℝ => (1 : ℝ) :=
  sum_vonMangoldt_div_sub_log_isBigO_one

-- The hypothesis `1 ≤ N` of `sum_primesLE_log_div_le` is not needed: at `N = 0` the sum is empty.
example : ∑ p ∈ Nat.primesLE 0, Real.log p / (p : ℝ) ≤
    Real.log ((0 : ℕ) : ℝ) + (Real.log 4 + 6) := by
  simp only [Nat.primesLE_zero, Finset.sum_empty, Nat.cast_zero, Real.log_zero, zero_add]
  positivity
