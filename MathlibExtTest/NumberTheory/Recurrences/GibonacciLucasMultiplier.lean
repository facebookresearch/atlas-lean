/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.GibonacciLucasMultiplier
import Mathlib.Tactic.NormNum

/-! # Tests for the Lucas multiplier identity -/

namespace MetaMathlibExt.gibonacci_add_neg_one_pow_mul_eq_lucas_mul.Tests

-- A negative odd shift reverses the sign of both the reflected term and the Lucas multiplier.
example (G : ℤ → ℝ) (hG : ∀ j : ℤ, G (j + 2) = G (j + 1) + G j) (s : ℤ) :
    G (s - 3) - G (s + 3) = -4 * G s := by
  have h := gibonacci_add_neg_one_pow_mul_eq_lucas_mul
    (fun m => (Int.fib (m - 1) + Int.fib (m + 1) : ℝ)) (fun _ => rfl) G hG (-3) s
  norm_num [sub_eq_add_neg, show Int.fib (-4) = -3 from rfl] at h ⊢
  exact h

-- Taking the center and the shift equal gives Fibonacci doubling on all integer indices.
example (r : ℤ) :
    (Int.fib (2 * r) : ℝ) = (Int.fib (r - 1) + Int.fib (r + 1) : ℝ) * Int.fib r := by
  have hfib (j : ℤ) : (Int.fib (j + 2) : ℝ) = Int.fib (j + 1) + Int.fib j := by
    rw [Int.fib_add_two, Int.cast_add, add_comm]
  simpa [two_mul] using gibonacci_add_neg_one_pow_mul_eq_lucas_mul
    (fun m => (Int.fib (m - 1) + Int.fib (m + 1) : ℝ)) (fun _ => rfl)
    (fun j => (Int.fib j : ℝ)) hfib r r

end MetaMathlibExt.gibonacci_add_neg_one_pow_mul_eq_lucas_mul.Tests
