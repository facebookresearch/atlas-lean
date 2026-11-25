/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.DivisibilityRuns

namespace MetaMathlibExt

-- At the first allowed index the two seeds can cancel.
example : Int.gcd (gibonacciNumber (-6) 6 2) (-6) = 6 :=
  int_gcd_gibonacciNumber_sub_two (-6) 6 2 (by decide)

example (n : ℕ) (hn : 2 ≤ n) :
    Int.gcd (gibonacciNumber (-12) 18 n) (gibonacciNumber (-12) 18 (n - 2)) = 6 :=
  int_gcd_gibonacciNumber_sub_two (-12) 18 n hn

example (n : ℕ) (hn : 2 ≤ n) :
    Int.gcd (gibonacciNumber 0 0 n) (gibonacciNumber 0 0 (n - 2)) = 0 :=
  int_gcd_gibonacciNumber_sub_two 0 0 n hn

-- At the first allowed index the backward recurrence reaches both seeds: `P₂ = P₃ - y` and
-- `x = P₃ - 2 y`.
example (x y : ℤ) :
    gibonacciNumber x y 2 = gibonacciNumber x y 3 - y ∧ x = gibonacciNumber x y 3 - 2 * y :=
  gibonacciNumber_backward x y 3 le_rfl

-- From the Lucas numbers `L₅ = 11` and `L₃ = 4`, the backward recurrence gives `L₄ = 7` and
-- `L₂ = 3`.
example : gibonacciNumber 2 1 4 = 7 ∧ gibonacciNumber 2 1 2 = 3 := by
  have h₅ : gibonacciNumber 2 1 5 = 11 := by decide
  have h₃ : gibonacciNumber 2 1 3 = 4 := by decide
  simpa [h₅, h₃] using gibonacciNumber_backward 2 1 5 (by decide)

-- Stepping back three places from `n + 3`, for every `n`.
example (x y : ℤ) (n : ℕ) :
    gibonacciNumber x y n = gibonacciNumber x y (n + 3) - 2 * gibonacciNumber x y (n + 1) := by
  simpa using (gibonacciNumber_backward x y (n + 3) (by omega)).2

-- The bound `3 ≤ n` is needed: at `n = 2` truncated subtraction gives `P (2 - 3) = P 0 = 1` for
-- the seeds `1, 0`, while `P 2 - 2 P 0 = 1 - 2 = -1`.
example :
    gibonacciNumber 1 0 (2 - 3) ≠ gibonacciNumber 1 0 2 - 2 * gibonacciNumber 1 0 (2 - 2) := by
  decide

-- Zero divides zero, but a run cannot start with a zero divisor.
example (y b c : ℤ) : ¬ IsDivRunUpTo 0 y 0 b c 1 := by
  simp [(isDivRunUpTo_small 0 y 0 b c).1]

-- For these signed seeds the first two divisibility checks hold, even with a zero dividend.
example (c : ℤ) : IsDivRunUpTo (-2) 5 0 10 c 3 ↔ 3 ∣ c := by
  rw [(isDivRunUpTo_small (-2) 5 0 10 c).2.2]
  norm_num

-- A zero third term ends the run even when the corresponding Tribonacci term is zero.
example : IsDivRunUpTo 2 (-2) 4 (-4) 0 2 := by decide
example : ¬ IsDivRunUpTo 2 (-2) 4 (-4) 0 3 := by decide

example : divRunCount 0 0 = 0 := by decide

end MetaMathlibExt
