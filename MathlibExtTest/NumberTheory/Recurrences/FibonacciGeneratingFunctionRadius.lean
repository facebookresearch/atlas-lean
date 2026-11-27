/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.FibonacciGeneratingFunctionRadius
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

open MetaMathlibExt Polynomial

local notation "F" => generalizedFibonacciPolynomial 0 1 (C (1 : ℤ) * X) (C 1)

-- The initial ratio is in the convergence interval and gives the value zero.
example : ∃ n : ℤ, (0 : ℚ) / (1 - 1 * (0 : ℚ) - 1 * (0 : ℚ) ^ 2) = n := by
  apply (fibonacciGenFun_eval_isInt_iff_of_abs_lt_radius
    (a := 1) (b := 1) (q := 0) (by decide) (by decide) (by decide) (by norm_num; positivity)).2
  exact ⟨0, by simp [generalizedFibonacciPolynomial]⟩

-- At the classical second ratio, integrality yields a witness for the even-index family.
example : ∃ i : ℕ, (1 / 2 : ℚ) = (((F (2 * i)).eval 1 : ℤ) : ℚ) /
    (((F (2 * i + 1)).eval 1 : ℤ) : ℚ) := by
  have hq : |((1 / 2 : ℚ) : ℝ)| < 2 / (↑(1 : ℕ) + Real.sqrt ((↑(1 : ℕ) : ℝ) ^ 2 + 4 * ↑(1 : ℕ))) := by
    norm_num
    have hs : Real.sqrt 5 < 3 := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
    exact (lt_div_iff₀ (by positivity)).2 (by linarith)
  exact (fibonacciGenFun_eval_isInt_iff_of_abs_lt_radius
    (a := 1) (b := 1) (q := 1 / 2) (by decide) (by decide) (by decide) hq).1 ⟨2, by norm_num⟩
