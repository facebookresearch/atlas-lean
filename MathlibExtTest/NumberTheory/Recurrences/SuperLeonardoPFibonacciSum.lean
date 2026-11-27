/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum
import MathlibExt.NumberTheory.Recurrences.SuperLeonardoPFibonacciSum

open MetaMathlibExt

-- The first recursive term is 4, not the 3 predicted by omitting the factor k.
example : superLeonardoP 1 2 (fun _ => 1) 2 = 4 := by
  rw [superLeonardoP_eq_fibonacciP_sum 1 2 (by decide) _ 2 (by decide)]
  norm_num [Finset.sum_range_succ, Nat.choose, fibonacciP_one, Nat.fib]

-- At n = p + 1, only the first and last initial values contribute.
example (k : ℕ) (x : ℕ → ℝ) : superLeonardoP 3 k x 4 = x 3 + x 0 + k := by
  rw [superLeonardoP_eq_fibonacciP_sum 3 k (by decide) x 4 (by decide)]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fibonacciP_eq_one 3 1 (by decide) (by decide), fibonacciP_eq_one 3 2 (by decide) (by decide)]

-- Farther into the recurrence, all initial values contribute with different coefficients.
example (k : ℕ) (x : ℕ → ℝ) :
    superLeonardoP 2 k x 8 = 6 * x 2 + (4 * x 0 + 3 * x 1) + 12 * k := by
  rw [superLeonardoP_eq_fibonacciP_sum 2 k (by decide) x 8 (by decide)]
  norm_num [Finset.sum_range_succ, Nat.choose,
    fibonacciP_eq_one 2 1 (by decide) (by decide), fibonacciP_eq_one 2 2 (by decide) (by decide),
    fibonacciP_rec 2 3 (by decide), fibonacciP_rec 2 4 (by decide), fibonacciP_rec 2 5 (by decide),
    fibonacciP_rec 2 6 (by decide), fibonacciP_rec 2 7 (by decide)]
