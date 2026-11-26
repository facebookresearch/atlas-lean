/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.LucasFibonacciTelescoping
import Mathlib.Tactic.NormNum.NatFib

/-! # Tests for the two Lucas–Fibonacci telescoping relations -/

namespace MetaMathlibExt.lucas_div_fib_sq_add_one_telescoping.Tests

-- At k = 0 the first denominator is one and the even Lucas number at zero is two.
example (L : ℤ → ℝ) (hL : ∀ m : ℤ, L m = Int.fib (m - 1) + Int.fib (m + 1)) :
    L 1 / 2 = 2 - L 2 / 2 ∧ L 1 / (2 * L 2) = 2 / L 2 - 1 / 2 := by
  have h := lucas_div_fib_sq_add_one_telescoping L hL 0
  have hzero : L 0 = 2 := by norm_num [hL]
  norm_num [hzero, Int.fib] at h ⊢
  exact h

-- At k = -2 both even Fibonacci numbers are negative and the odd Lucas number has negative index.
example (L : ℤ → ℝ) (hL : ∀ m : ℤ, L m = Int.fib (m - 1) + Int.fib (m + 1)) :
    L (-3) / 5 = L (-4) / 10 - L (-2) / 2 ∧
      L (-3) / (L (-4) * L (-2)) * 4 = 2 / L (-2) - 10 / L (-4) := by
  have h := lucas_div_fib_sq_add_one_telescoping L hL (-2)
  norm_num [Int.fib] at h
  exact h

end MetaMathlibExt.lucas_div_fib_sq_add_one_telescoping.Tests
