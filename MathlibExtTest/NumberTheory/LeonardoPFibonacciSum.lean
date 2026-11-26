/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.LeonardoPFibonacciSum

open MetaMathlibExt MathlibExt.NumberTheory.LeonardoPWanted

-- The shortest window at the first allowed index also permits k = 0.
example : ∑ i ∈ Finset.range 2, (fibonacciP 1 (1 + i) : ℤ) = 2 := by
  calc
    _ = leonardoPK 1 0 2 := by simpa using succ_mul_sum_fibonacciP 1 0 1 (by decide) (by decide)
    _ = 2 := by decide

-- For p = 3 the four terms starting at index four correspond to Leonardo index nine.
example : 3 * ∑ i ∈ Finset.range 4, (fibonacciP 3 (4 + i) : ℤ) = 30 := by
  calc
    _ = leonardoPK 3 2 9 + 2 := succ_mul_sum_fibonacciP 3 2 4 (by decide) (by decide)
    _ = 30 := by decide

private theorem fibonacciP_three_four : fibonacciP 3 4 = 1 := by
  rw [fibonacciP_rec 3 4 (by decide)]
  change fibonacciP 3 3 + fibonacciP 3 0 = 1
  simp [fibonacciP_eq_one 3 3 (by decide) le_rfl]

-- At n = p the shifted Fibonacci index crosses its initial-value range.
example : leonardoPK 3 2 3 = 1 := by
  rw [leonardoPK_eq 3 2 3 (by decide) (by decide), fibonacciP_three_four]
  decide

-- The very next Leonardo term is the first to use the inhomogeneous recurrence.
example : leonardoPK 3 2 4 = 4 := by
  have h : fibonacciP 3 5 = 2 := by
    rw [fibonacciP_rec 3 5 (by decide)]
    change fibonacciP 3 4 + fibonacciP 3 1 = 2
    rw [fibonacciP_three_four, fibonacciP_eq_one 3 1 (by decide) (by decide)]
  rw [leonardoPK_eq 3 2 4 (by decide) (by decide), h]
  decide

-- At p = k = 1 the formula specializes to the ordinary Fibonacci numbers.
example (n : ℕ) : leonardoPK 1 1 n = 2 * (Nat.fib (n + 1) : ℤ) - 1 := by
  simpa [fibonacciP_one] using leonardoPK_eq 1 1 n (by decide) (by decide)
