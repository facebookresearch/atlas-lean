/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import MathlibExt.NumberTheory.Recurrences.LucasGenFunIntegerInRadius

/-! # Tests for the generalized Lucas generating function inside its radius -/

open MetaMathlibExt Polynomial

local notation "A" => C (2 : ℤ) * X
local notation "B" => C (2 : ℤ)
local notation "F" => generalizedFibonacciPolynomial 0 1 A B
local notation "L" => generalizedFibonacciPolynomial 2 A A B
local notation "atOne(" p ")" => ((Polynomial.eval (1 : ℤ) p : ℤ) : ℚ)
local notation "value(" q ")" => ((2 - 2 * (q : ℚ)) / (1 - 2 * q - 2 * q ^ 2))
local notation "radius" => (2 / (2 + Real.sqrt 12) : ℝ)

private theorem third_lt_radius : (1 / 3 : ℝ) < radius := by
  have hs : Real.sqrt 12 < 4 := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  exact (lt_div_iff₀ (by positivity)).2 (by linarith)

-- Both positive examples use b = 2, so the power of b in the classification is nontrivial.
example : |((1 / 3 : ℚ) : ℝ)| < radius ∧
    (1 / 3 : ℚ) = atOne(F 2) / atOne(F 3) ∧ value(1 / 3) = (12 : ℤ) := by
  refine ⟨?_, ?_, by norm_num⟩
  · simpa using third_lt_radius
  · change (1 / 3 : ℚ) = atOne(F (0 + 2)) / atOne(F (1 + 2))
    norm_num

example : |((1 / 4 : ℚ) : ℝ)| < radius ∧
    (1 / 4 : ℚ) = atOne(L 1) / atOne(L 2) ∧ value(1 / 4) = (4 : ℤ) := by
  refine ⟨?_, ?_, by norm_num⟩
  · norm_num
    exact (by norm_num : (1 / 4 : ℝ) < 1 / 3).trans third_lt_radius
  · change (1 / 4 : ℚ) = atOne(L 1) / atOne(L (0 + 2))
    norm_num

example : |((0 : ℚ) : ℝ)| < radius ∧ (0 : ℚ) = atOne(F 0) / atOne(F 1) ∧
    value(0) = (2 : ℤ) := by
  refine ⟨?_, by norm_num, by norm_num⟩
  norm_num
  positivity

private theorem eval_nonneg (s₀ s₁ : ℤ[X]) (h₀ : 0 ≤ s₀.eval 1) (h₁ : 0 ≤ s₁.eval 1) (n : ℕ) :
    0 ≤ (generalizedFibonacciPolynomial s₀ s₁ A B n).eval 1 := by
  induction n using Nat.twoStepInduction with
  | zero => simpa using h₀
  | one => simpa using h₁
  | more n ih₀ ih₁ =>
    simp only [generalizedFibonacciPolynomial_add_two, eval_add, eval_mul, eval_C, eval_X, mul_one]
    exact add_nonneg (mul_nonneg (by norm_num) ih₁) (mul_nonneg (by norm_num) ih₀)

-- A negative input strictly inside the radius has neither form and gives a noninteger.
example : |((-1 / 4 : ℚ) : ℝ)| < radius ∧ value(-1 / 4) = 20 / 11 ∧
    (¬ ∃ z : ℤ, value(-1 / 4) = z) ∧
    ¬ ∃ i : ℕ, (-1 / 4 : ℚ) = atOne(F (2 * i)) / atOne(F (2 * i + 1)) ∨
      (-1 / 4 : ℚ) = atOne(L (2 * i + 1)) / atOne(L (2 * i + 2)) := by
  have hF (n : ℕ) : (0 : ℚ) ≤ atOne(F n) := by
    exact_mod_cast eval_nonneg 0 1 (by norm_num) (by norm_num) n
  have hL (n : ℕ) : (0 : ℚ) ≤ atOne(L n) := by
    exact_mod_cast eval_nonneg 2 A (by norm_num) (by norm_num) n
  refine ⟨?_, by norm_num, ?_, ?_⟩
  · norm_num
    exact (by norm_num : (1 / 4 : ℝ) < 1 / 3).trans third_lt_radius
  · rintro ⟨z, hz⟩
    have h₁ : (1 : ℚ) < value(-1 / 4) := by norm_num
    have h₂ : value(-1 / 4) < (2 : ℚ) := by norm_num
    rw [hz] at h₁ h₂
    have hz₁ : (1 : ℤ) < z := by exact_mod_cast h₁
    have hz₂ : z < (2 : ℤ) := by exact_mod_cast h₂
    omega
  · rintro ⟨i, hi | hi⟩
    · have h := div_nonneg (hF (2 * i)) (hF (2 * i + 1))
      rw [← hi] at h
      norm_num at h
    · have h := div_nonneg (hL (2 * i + 1)) (hL (2 * i + 2))
      rw [← hi] at h
      norm_num at h

-- Client check: the theorem recovers a ratio witness from the independently computed value.
example : ∃ i : ℕ, (1 / 3 : ℚ) = atOne(F (2 * i)) / atOne(F (2 * i + 1)) ∨
    (1 / 3 : ℚ) = atOne(L (2 * i + 1)) / atOne(L (2 * i + 2)) := by
  have hq : |((1 / 3 : ℚ) : ℝ)| < 2 / (↑(2 : ℕ) + Real.sqrt (↑(2 : ℕ) ^ 2 + 4 * ↑(2 : ℕ))) := by
    norm_num
    exact third_lt_radius
  exact (lucasGenFun_eval_isInt_iff_of_abs_lt_radius (a := 2) (b := 2)
    (by decide) (by decide) (by decide) (by decide) hq).mp ⟨12, by norm_num⟩
