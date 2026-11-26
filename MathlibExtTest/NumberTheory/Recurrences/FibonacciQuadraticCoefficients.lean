/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.FibonacciQuadraticCoefficients
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace MetaMathlibExt

-- The paper's example has initial values 0, 0, 1, 4, 12, 31.
example (n : ℕ) : ∃ k : ℤ, (k : ℚ) =
    ((5 * n ^ 2 - n - 4) / 25) * Nat.fib n +
      ((5 * n ^ 2 + n) / 50) * ((Nat.fib (n + 1) : ℚ) - Nat.fib n) := by
  obtain ⟨k, hk⟩ := (fib_quadratic_coeff_isInt_iff
    (1 / 5) (-1 / 25) (-4 / 25) (1 / 10) (1 / 50) 0).2
    ⟨⟨0, by norm_num⟩, 0, 1, 4, 12, 31, by norm_num⟩ n
  exact ⟨k, hk.trans (by ring)⟩

-- Even when both leading coefficients vanish, the term at zero forces integral f.
example : ¬ ∀ n : ℕ, ∃ k : ℤ, (k : ℚ) = 1 / 2 * ((Nat.fib (n + 1) : ℚ) - Nat.fib n) := by
  intro h
  obtain ⟨k, hk⟩ := ((fib_quadratic_coeff_isInt_iff 0 0 0 0 0 (1 / 2)).1 (by simpa using h)).1
  have hden : (1 / 2 : ℚ).den = 1 := by rw [← hk, Rat.den_intCast]
  exact (by decide : ¬ (2 : ℕ) ∣ 1)
    ((Rat.den_div_natCast_eq_one_iff 1 2 (by decide)).mp hden)

end MetaMathlibExt
