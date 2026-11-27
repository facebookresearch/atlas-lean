/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.GreedyOddFibonacciFloor

open Finset MetaMathlibExt

-- Every prefix of the zero representation satisfies the strict greedy bound.
example (n : ℕ) : ⌊(0 : ℝ) * Real.goldenRatio⌋₊ = 0 ∧
    ⌊(0 : ℝ) * (1 + Real.goldenRatio)⌋₊ = 0 := by
  simpa only [zero_mul, sum_const_zero, Nat.cast_zero] using
    floor_greedy_odd_fib_sum_mul_goldenRatio n (fun _ ↦ 0)
      (fun m _ ↦ by simp [Nat.fib_pos])

-- The greedy digits of 11 include a doubled place and allow a leading zero: 11 = 1 + 2 F₅.
example : ⌊(11 : ℝ) * Real.goldenRatio⌋₊ = 17 ∧
    ⌊(11 : ℝ) * (1 + Real.goldenRatio)⌋₊ = 28 := by
  let a (k : ℕ) : ℕ := if k = 0 then 1 else if k = 2 then 2 else 0
  have ha : ∀ m ≤ 3 + 1, ∑ k ∈ range m, a k * Nat.fib (2 * k + 1) < Nat.fib (2 * m + 1) := by
    intro m hm
    interval_cases m <;> decide
  simpa [a, sum_range_succ, Nat.fib_add_two] using
    floor_greedy_odd_fib_sum_mul_goldenRatio 3 a ha
