/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.FibonacciLinearCoefficients
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace MetaMathlibExt

-- The source's introductory example: `d = 0` and `(z₁, z₂, z₃) = (1, 1, 3)` give
-- `(2n + 3)/5 · F_n - n/5 · F_{n-1}`, with values 0, 1, 1, 3, 5, 10, ...
example (n : ℕ) : ∃ k : ℤ, (k : ℚ) =
    ((2 * n + 3) / 5) * Nat.fib n - (n / 5) * ((Nat.fib (n + 1) : ℚ) - Nat.fib n) := by
  obtain ⟨k, hk⟩ := (fib_linear_coeff_isInt_iff (2 / 5) (3 / 5) (-1 / 5) 0).2
    ⟨⟨0, by norm_num⟩, 1, 1, 3, by norm_num⟩ n
  refine ⟨k, hk.trans ?_⟩
  ring

-- Both leading coefficients may vanish (the source excludes this case): the Lucas numbers
-- `L_n = F_n + 2 F_{n-1}` correspond to `d = 2` and `(z₁, z₂, z₃) = (1, 1, 2)`.
example (n : ℕ) : ∃ k : ℤ, (k : ℚ) = Nat.fib n + 2 * ((Nat.fib (n + 1) : ℚ) - Nat.fib n) := by
  obtain ⟨k, hk⟩ := (fib_linear_coeff_isInt_iff 0 1 0 2).2
    ⟨⟨2, by norm_num⟩, 1, 1, 2, by norm_num⟩ n
  refine ⟨k, hk.trans ?_⟩
  ring

-- The forward direction rules out `n F_{n-1} / 5`: its coefficient formulas force `5 z = 1`
-- for some integer `z`.
example : ¬ ∀ n : ℕ, ∃ k : ℤ, (k : ℚ) = (n / 5) * ((Nat.fib (n + 1) : ℚ) - Nat.fib n) := by
  intro h
  obtain ⟨-, z₁, z₂, z₃, ha, hb, hc⟩ := (fib_linear_coeff_isInt_iff 0 0 (1 / 5) 0).1
    fun n => (h n).imp fun k hk => hk.trans (by ring)
  have h₁ : ((-z₁ - 3 * z₂ + 2 * z₃ : ℤ) : ℚ) = 0 := by linarith
  have h₂ : ((6 * z₁ + 3 * z₂ - 2 * z₃ : ℤ) : ℚ) = 0 := by linarith
  have h₃ : ((-2 * z₁ + 4 * z₂ - z₃ : ℤ) : ℚ) = 1 := by linarith
  norm_cast at h₁ h₂ h₃
  omega

end MetaMathlibExt
