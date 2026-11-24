/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum
import MathlibExt.NumberTheory.Recurrences.GibonacciIndexDoubling

/-! # Tests for the gibonacci index-doubling identity -/

open MetaMathlibExt

-- With k = 0 the identity holds for every integer shift, without a seed assumption.
example (G : ℤ → ℝ) (hG : ∀ j : ℤ, G (j + 2) = G (j + 1) + G j) (s : ℤ) :
    G s = G (s + 1) - G (s - 1) := by
  simpa using gibonacci_two_mul_add_eq_fib_sq_combination G hG 0 s

-- At k = -2 and s = -1 the signed Fibonacci coefficients are 1, 1, and -4.
example (G : ℤ → ℝ) (hG : ∀ j : ℤ, G (j + 2) = G (j + 1) + G j) :
    G (-5) = G 0 + G (-1) - 4 * G (-2) := by
  have h := gibonacci_two_mul_add_eq_fib_sq_combination G hG (-2) (-1)
  norm_num [show Int.fib (-3) = 2 by rfl] at h
  exact h
