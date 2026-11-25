/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.GibonacciDOcagneIdentity
import Mathlib.Data.Int.Fib.Basic
import Mathlib.Tactic.LinearCombination

/-! # Tests for the d'Ocagne-type identity for two gibonacci sequences -/

namespace MetaMathlibExt.gibonacci_dOcagne_type_identity.Tests

-- For a negative odd shift both signs reverse, and both seeds contribute.
example (G H : ℤ → ℝ) (hG : ∀ j : ℤ, G (j + 2) = G (j + 1) + G j)
    (hH : ∀ j : ℤ, H (j + 2) = H (j + 1) + H j) :
    H 0 * G (-1) - H 1 * G (-2) =
      (H 2 + H 0) * G (-1) - (G 0 * H (-1) + G 1 * H 0) := by
  simpa [sub_eq_add_neg] using gibonacci_dOcagne_type_identity G H hG hH (-1) 1 (-2)

-- Consecutive shifts of the signed Fibonacci sequence give Cassini's identity on all of ℤ.
example (r : ℤ) :
    (Int.fib r : ℝ) * Int.fib (r + 2) - (Int.fib (r + 1) : ℝ) ^ 2 = -(-1 : ℝ) ^ r := by
  have hfib (j : ℤ) : (Int.fib (j + 2) : ℝ) = Int.fib (j + 1) + Int.fib j := by
    rw [Int.fib_add_two, Int.cast_add, add_comm]
  have h := gibonacci_dOcagne_type_identity (fun j => (Int.fib (j + 1) : ℝ))
    (fun j => (Int.fib j : ℝ)) (fun j => by
      simpa only [add_right_comm j 1 2] using hfib (j + 1)) hfib r 0 r
  simp [zpow_sub_one₀, show r + 1 + 1 = r + 2 by omega] at h
  linear_combination h

end MetaMathlibExt.gibonacci_dOcagne_type_identity.Tests
