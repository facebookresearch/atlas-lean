/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.LucasNumberGeneratingFunctionValues
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

open MetaMathlibExt

private lemma in_radius {x : ℝ} (hx : |x| ≤ 3 / 5) : |x| < 2 / (1 + Real.sqrt 5) := by
  apply hx.trans_lt
  apply (lt_div_iff₀ (by positivity)).2
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  nlinarith

-- The exceptional negative input and a noninitial member of each ratio family.
example : ∃ n : ℤ, (2 - (-1 / 2 : ℚ)) / (1 - (-1 / 2 : ℚ) - (-1 / 2 : ℚ) ^ 2) = n := by
  apply (lucasNumberGenFun_eval_isInt_iff_of_abs_lt_radius (in_radius (by norm_num))).2
  exact Or.inr rfl

example : ∃ n : ℤ, (2 - (3 / 5 : ℚ)) / (1 - (3 / 5 : ℚ) - (3 / 5 : ℚ) ^ 2) = n := by
  apply (lucasNumberGenFun_eval_isInt_iff_of_abs_lt_radius (in_radius (by norm_num))).2
  exact Or.inl ⟨2, Or.inl (by norm_num [Nat.fib])⟩

example : ∃ n : ℤ, (2 - (4 / 7 : ℚ)) / (1 - (4 / 7 : ℚ) - (4 / 7 : ℚ) ^ 2) = n := by
  apply (lucasNumberGenFun_eval_isInt_iff_of_abs_lt_radius (in_radius (by norm_num))).2
  exact Or.inl ⟨1, Or.inr (by norm_num [lucasNumber])⟩

-- At 1/4 the value is 28/11, ruling out both ratio families at every index.
example (i : ℕ) :
    (1 / 4 : ℚ) ≠ (Nat.fib (2 * i) : ℚ) / Nat.fib (2 * i + 1) ∧
      (1 / 4 : ℚ) ≠ (lucasNumber (2 * i + 1) : ℚ) / lucasNumber (2 * i + 2) := by
  apply not_or.mp
  intro h
  obtain ⟨n, hn⟩ := (lucasNumberGenFun_eval_isInt_iff_of_abs_lt_radius
    (q := 1 / 4) (in_radius (by norm_num))).2 (Or.inl ⟨i, h⟩)
  norm_num at hn
  have he : (28 : ℤ) = n * 11 := by exact_mod_cast (div_eq_iff (by norm_num)).1 hn
  omega
