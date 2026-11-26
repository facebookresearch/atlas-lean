/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.FibonacciGeneratingFunctionValues
import Mathlib.Tactic.NormNum

open MetaMathlibExt Polynomial

local notation "F" => generalizedFibonacciPolynomial 0 1 (C (8 : ℤ) * X) (C 4)

-- With nonsquarefree b = 4, F₃/F₄ reduces to 17/144.
example : ∃ n : ℤ, (17 / 144 : ℚ) / (1 - 8 * (17 / 144) - 4 * (17 / 144) ^ 2) = n := by
  apply (fibonacciGenFun_eval_isInt_iff (a := 8) (b := 4) (by decide) (by decide) (by decide) _).2
  exact Or.inl ⟨3, by norm_num [generalizedFibonacciPolynomial]⟩

-- The negative family uses b in the denominator: -F₃/(4 F₂) = -17/8.
example : ∃ n : ℤ, (-17 / 8 : ℚ) / (1 - 8 * (-17 / 8) - 4 * (-17 / 8) ^ 2) = n := by
  apply (fibonacciGenFun_eval_isInt_iff (a := 8) (b := 4) (by decide) (by decide) (by decide) _).2
  exact Or.inr ⟨2, by decide, by norm_num [generalizedFibonacciPolynomial]⟩

-- At q = 1 the value is -1/11, so 1 cannot be a consecutive ratio at any index.
example (i : ℕ) :
    (1 : ℚ) ≠ (((F i).eval 1 : ℤ) : ℚ) / (((F (i + 1)).eval 1 : ℤ) : ℚ) := by
  intro h
  obtain ⟨n, hn⟩ := (fibonacciGenFun_eval_isInt_iff (a := 8) (b := 4)
    (by decide) (by decide) (by decide) 1).2 (Or.inl ⟨i, h⟩)
  norm_num at hn
  rw [← neg_div] at hn
  have he : (-1 : ℤ) = n * 11 := by exact_mod_cast (div_eq_iff (by norm_num)).mp hn
  omega
