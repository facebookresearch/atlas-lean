/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.SuperLeonardoPBinomial
import Mathlib.Tactic.NormNum

open MetaMathlibExt

-- The first recursive term detects the missing factor in the printed formula.
example : superLeonardoP 1 2 (fun _ => 1) 2 = 4 := by
  rw [superLeonardoP_eq_sum_choose 1 2 (by decide) _ 2 (by decide)]
  norm_num [Finset.sum_range_succ, Nat.choose]

-- All three initial values and the accumulated increment have distinct coefficients.
example (k : ℕ) (x : ℕ → ℝ) :
    superLeonardoP 2 k x 6 = 3 * x 2 + (2 * x 0 + x 1) + 5 * k := by
  rw [superLeonardoP_eq_sum_choose 2 k (by decide) x 6 (by decide)]
  norm_num [Finset.sum_range_succ, Nat.choose]

-- At p = 1 the Fibonacci formula is the classical sum along shallow diagonals of Pascal's triangle.
example (n : ℕ) : Nat.fib (n + 1) = ∑ i ∈ Finset.range (n / 2 + 1), (n - i).choose i := by
  rw [← fibonacciP_one, fibonacciP_succ_eq_sum_choose 1 n le_rfl]
  simp

-- The last summand is needed: F_2(7) = C(6, 0) + C(4, 1) + C(2, 2) = 6.
example : fibonacciP 2 7 = 6 := by
  rw [fibonacciP_succ_eq_sum_choose 2 6 (by decide)]
  decide

-- At the last initial index the sum includes the zero term C(1, 2).
example : superLeonardoP 2 1 (fun i => (i : ℝ) + 1) 2 = 3 := by
  rw [superLeonardoP_one_succ_eq_sum_choose 2 (by decide)]
  norm_num [Finset.sum_range_succ, Nat.choose]

-- At n = 6 the last summand is nonzero: C(7, 1) + C(5, 2) + C(3, 3) = 18.
example : superLeonardoP 2 1 (fun i => (i : ℝ) + 1) 6 = 18 := by
  rw [superLeonardoP_one_succ_eq_sum_choose 2 (by decide)]
  norm_num [Finset.sum_range_succ, Nat.choose]
