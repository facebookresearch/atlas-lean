/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.GibonacciProductSum
import Mathlib.Data.Int.Fib.Basic
import Mathlib.Tactic.NormNum.NatFib

/-! # Tests for the sum of products of two gibonacci sequences -/

namespace MetaMathlibExt

private def fib (j : ℤ) : ℝ := Int.fib j

private theorem fib_rec (j : ℤ) : fib (j + 2) = fib (j + 1) + fib j := by
  simp only [fib, Int.fib_add_two, Int.cast_add]
  exact add_comm _ _

-- The empty interval cancels the endpoints for arbitrary integer shifts.
example (G H : ℤ → ℝ) (hG : ∀ j : ℤ, G (j + 2) = G (j + 1) + G j)
    (hH : ∀ j : ℤ, H (j + 2) = H (j + 1) + H j) (k s : ℤ) :
    0 = G k * H (s + 1) + G (k + 1) * H s - G (k + 1) * H s - G k * H (s + 1) := by
  have hIcc : Finset.Icc 1 (0 : ℕ) = ∅ := by decide
  simpa only [hIcc, Finset.sum_empty, mul_zero, Nat.cast_zero, zero_add] using
    two_mul_sum_gibonacci_mul_gibonacci G H hG hH 0 k s

-- At n = 1 the sum is 1, so the endpoints give 2, not 1.
example : fib 1 * fib 2 + fib 2 * fib 1 - fib 1 * fib 0 - fib 0 * fib 1 = 2 := by
  have h := two_mul_sum_gibonacci_mul_gibonacci fib fib fib_rec fib_rec 1 0 0
  have hsum : 2 * ∑ j ∈ Finset.Icc 1 (1 : ℕ), fib (j + (0 : ℤ)) * fib (j + (0 : ℤ)) = 2 := by
    norm_num [fib, Int.fib]
  rw [hsum] at h
  exact h.symm

-- With distinct sequences and shifts (-3, 2), the two summands are -3 and 5.
example :
    fib (-1) * fib 6 + fib 0 * fib 5 - fib (-2) * fib 3 - fib (-3) * fib 4 = 4 := by
  have hShift (j : ℤ) : fib (j + 2 + 1) = fib (j + 1 + 1) + fib (j + 1) := by
    rw [add_right_comm j 2 1]
    exact fib_rec (j + 1)
  have h := two_mul_sum_gibonacci_mul_gibonacci fib (fun j => fib (j + 1)) fib_rec hShift 2 (-3) 2
  have hsum : 2 * ∑ j ∈ Finset.Icc 1 (2 : ℕ), fib (j + (-3 : ℤ)) * fib (j + (2 : ℤ) + 1) = 4 := by
    have hIcc : Finset.Icc 1 (2 : ℕ) = {1, 2} := by decide
    norm_num [hIcc, Finset.sum_insert, fib, Int.fib]
  rw [hsum] at h
  exact h.symm

end MetaMathlibExt
