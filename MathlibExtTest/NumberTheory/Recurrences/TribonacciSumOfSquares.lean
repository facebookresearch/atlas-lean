/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.TribonacciSumOfSquares
import MathlibExt.NumberTheory.TribonacciInt
import Mathlib.Tactic.NormNum

/-! # Tests for `MathlibExt.NumberTheory.Recurrences.TribonacciSumOfSquares` -/

namespace MathlibExtTest.TribonacciSumOfSquares

open MathlibExt.NumberTheory.Recurrences.TribonacciTetranacciSumsOfSquaresWanted MetaMathlibExt

-- Test section: the two-sided Tribonacci sequence `tribonacciInt` (`T 0 = 0`, `T 1 = T 2 = 1`,
-- `T (-1) = 0`) satisfies the hypothesis, so the identity is not vacuous. For `n = 10` the closed
-- form, `4 * 149 * 274 - 0 - (274 - 81) ^ 2 + 1 ^ 2`, is four times the sum of the squares of
-- `1, 1, 2, 4, 7, 13, 24, 44, 81, 149`.
example : 4 * ∑ k ∈ Finset.Icc (1 : ℕ) 10, tribonacciInt k ^ 2 = 4 * 31514 := by
  rw [four_mul_sum_tribonacci_sq tribonacciInt tribonacciInt_add_three 10]
  decide

example : ∑ k ∈ Finset.Icc (1 : ℕ) 10, tribonacciInt k ^ 2 = 31514 := by decide

-- Test section: the boundary terms. For `tribonacciInt` they are `4 * T 0 * T 1 = 0` and
-- `(T 1 - T (-1)) ^ 2 = 1`; the sequence shifted by two places has `4 * S 0 * S 1 = 8` and
-- `(S 1 - S (-1)) ^ 2 = 1`, and the closed form still gives four times the sum of squares.

/-- The two-sided Tribonacci sequence shifted by two places, `S m = tribonacciInt (m + 2)`. -/
private def S (m : ℤ) : ℤ := tribonacciInt (m + 2)

private theorem S_add_three (m : ℤ) : S (m + 3) = S (m + 2) + S (m + 1) + S m := by
  simpa only [S, add_right_comm _ _ (2 : ℤ)] using tribonacciInt_add_three (m + 2)

example : (S (-1), S 0, S 1, S 2, S 3, S 4, S 5) = (1, 1, 2, 4, 7, 13, 24) := by decide

example : 4 * ∑ k ∈ Finset.Icc (1 : ℕ) 4, S k ^ 2 =
    4 * 13 * 24 - 4 * 1 * 2 - (24 - 7) ^ 2 + (2 - 1) ^ 2 := by
  rw [four_mul_sum_tribonacci_sq S S_add_three 4]
  decide

example : ∑ k ∈ Finset.Icc (1 : ℕ) 4, S k ^ 2 = 2 ^ 2 + 4 ^ 2 + 7 ^ 2 + 13 ^ 2 := by decide

-- Test section: the hypotheses are needed. Without the recurrence the identity fails: for the
-- constant sequence `1` at `n = 1`, the left side is `4` and the right side is `4 - 4 - 0 + 0`.
example : ¬ ∀ (T : ℤ → ℤ) (n : ℕ), 4 * (∑ k ∈ Finset.Icc 1 n, (T k) ^ 2) =
    4 * T n * T ((n : ℤ) + 1) - 4 * T 0 * T 1 -
      (T ((n : ℤ) + 1) - T ((n : ℤ) - 1)) ^ 2 + (T 1 - T (-1)) ^ 2 := by
  intro h
  have := h (fun _ => 1) 1
  norm_num at this

-- The recurrence is also needed at the negative index `-1`, where it ties `T (-1)` to `T 0`,
-- `T 1` and `T 2`. Changing `tribonacciInt` to `5` at `-1` keeps the recurrence at every `m ≥ 0`,
-- but at `n = 1` the left side is `4` and the right side is `4 - 0 - 1 + (1 - 5) ^ 2 = 19`.
example : ¬ ∀ T : ℤ → ℤ, (∀ m : ℤ, 0 ≤ m → T (m + 3) = T (m + 2) + T (m + 1) + T m) →
    ∀ n : ℕ, 4 * (∑ k ∈ Finset.Icc 1 n, (T k) ^ 2) =
      4 * T n * T ((n : ℤ) + 1) - 4 * T 0 * T 1 -
        (T ((n : ℤ) + 1) - T ((n : ℤ) - 1)) ^ 2 + (T 1 - T (-1)) ^ 2 := by
  intro h
  have := h (fun m => if m = -1 then 5 else tribonacciInt m) (fun m hm => by
    simp only [show m + 3 ≠ -1 by omega, show m + 2 ≠ -1 by omega, show m + 1 ≠ -1 by omega,
      show m ≠ -1 by omega, ↓reduceIte]
    exact tribonacciInt_add_three m) 1
  revert this
  decide

end MathlibExtTest.TribonacciSumOfSquares
