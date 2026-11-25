/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.FibonacciPolynomialCoefficients
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace MetaMathlibExt

-- The tiling example in the paper has initial values 0, 1, 2, 6, 12, 26.
example (n : ℕ) : ∃ k : ℤ, (k : ℚ) =
    ((4 * n - 4) / 5) * Nat.fib n +
      (3 * n / 5) * ((Nat.fib (n + 1) : ℚ) - Nat.fib n) + 1 / 2 - 1 / 2 * (-1) ^ n := by
  obtain ⟨k, hk⟩ := (fib_linear_coeff_add_alternating_isInt_iff
    (4 / 5) (-4 / 5) (3 / 5) 0 (1 / 2) (-1 / 2)).2 ⟨0, 1, 2, 6, 12, 26, by norm_num⟩ n
  refine ⟨k, hk.trans ?_⟩
  ring

-- With both Fibonacci coefficients zero, the terms can alternate between 0 and −1.
example (n : ℕ) : ∃ k : ℤ, (k : ℚ) = -1 / 2 + 1 / 2 * (-1) ^ n := by
  simpa using (fib_linear_coeff_add_alternating_isInt_iff 0 0 0 0 (-1 / 2) (1 / 2)).2
    ⟨0, -1, 0, -1, 0, -1, by norm_num⟩ n

end MetaMathlibExt
