/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.GibonacciLucasLikeSum
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum.NatFib

/-! # Tests for the gibonacci identity with Lucas-type sums -/

namespace MetaMathlibExt.gibonacci_lucas_like_mul_add_eq_fib_mul.Tests

-- With H the Fibonacci sequence, the shift r = -2 has F_r = -1 and tests both seeds of G.
example (G : ℤ → ℝ) (hG : ∀ j : ℤ, G (j + 2) = G (j + 1) + G j) :
    2 * G 3 - 3 * G 5 = -7 * G 0 - 11 * G 1 := by
  have hF (j : ℤ) : (Int.fib (j + 2) : ℝ) = Int.fib (j + 1) + Int.fib j := by
    rw [Int.fib_add_two, Int.cast_add, add_comm]
  have h := gibonacci_lucas_like_mul_add_eq_fib_mul G (fun j => (Int.fib j : ℝ))
    hG hF (-2) 2 3
  norm_num [Int.fib] at h
  linear_combination h

end MetaMathlibExt.gibonacci_lucas_like_mul_add_eq_fib_mul.Tests

namespace MetaMathlibExt.gibonacci_seed_lucas_like_identity.Tests

-- Take H to be the signed Fibonacci sequence, with k = -3 and r = -2.
-- The four nonzero coefficients test both seeds of G and both terms on the right.
example (G : ℤ → ℝ) (hG : ∀ j : ℤ, G (j + 2) = G (j + 1) + G j) :
    18 * G 0 - 11 * G 1 = 7 * G (-2) - 4 * G (-1) := by
  have hF (j : ℤ) : (Int.fib (j + 2) : ℝ) = Int.fib (j + 1) + Int.fib j := by
    rw [Int.fib_add_two, Int.cast_add, add_comm]
  have h := gibonacci_seed_lucas_like_identity G (fun j => (Int.fib j : ℝ)) hG hF (-3) (-2)
  norm_num [Int.fib, Int.even_iff] at h
  linear_combination h

end MetaMathlibExt.gibonacci_seed_lucas_like_identity.Tests
