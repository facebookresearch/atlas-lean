/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.WeightedHigherFibSum
import Mathlib.Data.Int.Fib.Basic
import Mathlib.Tactic.NormNum

/-! # Tests for weighted sums of higher-order Fibonacci sequences -/

namespace MathlibExt.NumberTheory.Recurrences.HigherFibonacciWalksWanted

-- A negative upper limit and the first nonempty sum at zero weight.
example (F : ℤ → ℚ) (m : ℕ) (l : ℤ) (q : ℚ) :
    weightedHigherFibSum F m (-1) l q = 0 := by
  simp [weightedHigherFibSum]

example (F : ℤ → ℚ) (m : ℕ) (l : ℤ) : weightedHigherFibSum F m 0 l 0 = F l := by
  simp [weightedHigherFibSum]

-- At order one the double sum is empty, leaving the finite geometric sum.
example (a : ℚ) (n : ℕ) (l : ℤ) :
    weightedHigherFibSum (fun _ => a) 1 n l 2 = 2 ^ (n + 1) * a - a := by
  have hrec : IsHigherFibRecurrence 1 (fun _ => a) := by
    intro k
    simp
  have h := weightedHigherFibSum_eq 1 le_rfl _ hrec n l 2 (by norm_num)
  norm_num at h
  exact h

-- For Fibonacci numbers the sum starting at index -2 is -1 + 2 + 0 + 8.
example : weightedHigherFibSum (fun k => (Int.fib k : ℚ)) 2 3 (-2) 2 = 9 := by
  have hrec : IsHigherFibRecurrence 2 (fun k => (Int.fib k : ℚ)) := by
    intro k
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero, sub_zero, zero_add,
      Nat.cast_one]
    have h := Int.fib_add_two (k - 2)
    rw [show k - 2 + 2 = k by omega, show k - 2 + 1 = k - 1 by omega, add_comm] at h
    rw [show k - 1 - 1 = k - 2 by omega, ← Int.cast_add, ← h]
  have h := weightedHigherFibSum_eq 2 (by decide) _ hrec 3 (-2) 2 (by norm_num)
  norm_num [show Int.fib (-3) = 2 from rfl] at h
  exact h

end MathlibExt.NumberTheory.Recurrences.HigherFibonacciWalksWanted
