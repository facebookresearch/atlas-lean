/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.GibonacciFibonacciLucasIdentity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

open MetaMathlibExt

private def fibReal (j : ℤ) : ℝ := Int.fib j

private theorem fibReal_recurrence (j : ℤ) :
    fibReal (j + 2) = fibReal (j + 1) + fibReal j := by
  simpa only [fibReal, Int.cast_add] using congrArg (fun a : ℤ => (a : ℝ))
    ((Int.fib_add_two j).trans (add_comm _ _))

-- At k = 1, the right-hand sign is positive.
example (G : ℤ → ℝ) (hG : ∀ j : ℤ, G (j + 2) = G (j + 1) + G j) :
    5 * G 1 - (G 2 + G 0) = 2 * (G 1 + G (-1)) := by
  simpa [fibReal, Int.fib_two] using
    (five_fib_mul_gibonacci_sub_lucas_mul
      (fun m => fibReal (m - 1) + fibReal (m + 1)) (fun _ => rfl) G hG 1 0)

-- The identity also holds at a negative Fibonacci index.
example : 5 * fibReal (-1) - (-1 : ℝ) * (fibReal 0 + fibReal (-2)) = 4 := by
  have h := five_fib_mul_gibonacci_sub_lucas_mul
    (fun m => fibReal (m - 1) + fibReal (m + 1)) (fun _ => rfl) fibReal fibReal_recurrence (-1) 0
  norm_num [fibReal] at h ⊢
