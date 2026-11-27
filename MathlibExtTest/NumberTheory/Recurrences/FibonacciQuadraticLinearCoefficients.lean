/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.FibonacciQuadraticLinearCoefficients
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace MetaMathlibExt

-- The authors' example has `e = z₁ = z₂ = z₃ = 1` and `z₄ = 2`.
example (n : ℕ) : ∃ k : ℤ, (k : ℚ) =
    ((5 * n ^ 2 - 43 * n + 88) / 50) * Nat.fib n +
      ((14 * n + 50) / 50) * ((Nat.fib (n + 1) : ℚ) - Nat.fib n) := by
  obtain ⟨k, hk⟩ := (fib_quadratic_linear_coeff_isInt_iff
    (1 / 10) (-43 / 50) (44 / 25) (7 / 25) 1).2 ⟨⟨1, by norm_num⟩, 1, 1, 1, 2, by norm_num⟩ n
  exact ⟨k, hk.trans (by ring)⟩

-- With both leading coefficients zero, the formula includes the Lucas numbers.
example (n : ℕ) : ∃ k : ℤ, (k : ℚ) = Nat.fib n + 2 * ((Nat.fib (n + 1) : ℚ) - Nat.fib n) := by
  simpa using (fib_quadratic_linear_coeff_isInt_iff 0 0 1 0 2).2
    ⟨⟨2, by norm_num⟩, 1, 1, 2, 3, by norm_num⟩ n

-- A fractional `e` prevents integrality already at index zero.
example : ¬ ∀ n : ℕ, ∃ k : ℤ, (k : ℚ) = 1 / 2 * ((Nat.fib (n + 1) : ℚ) - Nat.fib n) := by
  intro h
  obtain ⟨k, hk⟩ := ((fib_quadratic_linear_coeff_isInt_iff 0 0 0 0 (1 / 2)).1
    (by simpa using h)).1
  have hden : (1 / 2 : ℚ).den = 1 := by rw [← hk, Rat.den_intCast]
  exact (by decide : ¬ (2 : ℕ) ∣ 1)
    ((Rat.den_div_natCast_eq_one_iff 1 2 (by decide)).mp hden)

end MetaMathlibExt
