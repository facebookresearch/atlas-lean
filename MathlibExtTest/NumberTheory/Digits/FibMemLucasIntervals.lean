/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Digits.FibMemLucasIntervals

/-!
# Tests for Fibonacci numbers in the Lucas intervals
-/

namespace MetaMathlibExt

-- At `n = 1` the Lucas intervals are `[L_2, L_3] = [3, 4]` and `[L_3 + 1, L_4 - 1] = [5, 6]`.
example : Nat.fib 4 ∈ Set.Icc 3 4 ∧ Nat.fib 5 ∈ Set.Icc 5 6 :=
  fib_mem_lucasIntervals 1 le_rfl

-- Both lower bounds are attained at `n = 1`: `F_4 = L_2` and `F_5 = L_3 + 1`.
example : Nat.fib 4 = lucasNumber 2 ∧ Nat.fib 5 = lucasNumber 3 + 1 := by decide

-- A larger instance: `F_12 = 144 ∈ [L_10, L_11] = [123, 199]` and
-- `F_13 = 233 ∈ [L_11 + 1, L_12 - 1] = [200, 321]`.
example : Nat.fib 12 ∈ Set.Icc 123 199 ∧ Nat.fib 13 ∈ Set.Icc 200 321 :=
  fib_mem_lucasIntervals 5 (by decide)

-- The hypothesis `1 ≤ n` is needed: at `n = 0` the even interval `[L_0, L_1] = [2, 1]` is empty,
-- so it does not contain `F_2 = 1`.
example : Nat.fib (2 * 0 + 2) ∉ Set.Icc (lucasNumber (2 * 0)) (lucasNumber (2 * 0 + 1)) := by
  decide

-- The truncated subtraction in the odd interval is harmless: the upper bound is strict.
example (n : ℕ) (hn : 1 ≤ n) : Nat.fib (2 * n + 3) < lucasNumber (2 * n + 2) := by
  have h := (fib_mem_lucasIntervals n hn).2.2
  have hL : lucasNumber (2 * n + 1) + 1 ≤ lucasNumber (2 * n + 2) - 1 :=
    (fib_mem_lucasIntervals n hn).2.1.trans h
  omega

end MetaMathlibExt
