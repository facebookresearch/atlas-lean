/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.QuadraticForm.NormForm
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity

@[expose] public section

example (K : Type) [Field K] (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    (∀ x₀ x₁ x₂ x₃ : K, x₀ ^ 2 - a * x₁ ^ 2 - b * x₂ ^ 2 + a * b * x₃ ^ 2 = 0 →
        x₀ = 0 ∧ x₁ = 0 ∧ x₂ = 0 ∧ x₃ = 0) ↔
      ∀ z x y : K, z ^ 2 - a * x ^ 2 - b * y ^ 2 = 0 → z = 0 ∧ x = 0 ∧ y = 0 :=
  QuadraticForm.forall_quaternary_normForm_eq_zero_iff_forall_ternary_eq_zero K a b ha hb

example : ∀ x₀ x₁ x₂ x₃ : ℚ,
    x₀ ^ 2 - (-1 : ℚ) * x₁ ^ 2 - (-1 : ℚ) * x₂ ^ 2 +
        (-1 : ℚ) * (-1 : ℚ) * x₃ ^ 2 = 0 →
    x₀ = 0 ∧ x₁ = 0 ∧ x₂ = 0 ∧ x₃ = 0 := by
  have htern : ∀ z x y : ℚ,
      z ^ 2 - (-1 : ℚ) * x ^ 2 - (-1 : ℚ) * y ^ 2 = 0 → z = 0 ∧ x = 0 ∧ y = 0 := by
    intro z x y hzy
    have hzy' : z ^ 2 + (x ^ 2 + y ^ 2) = 0 := by linear_combination hzy
    obtain ⟨hz2, hxy⟩ :=
      (add_eq_zero_iff_of_nonneg (sq_nonneg z) (by positivity)).mp hzy'
    obtain ⟨hx2, hy2⟩ :=
      (add_eq_zero_iff_of_nonneg (sq_nonneg x) (sq_nonneg y)).mp hxy
    exact ⟨sq_eq_zero_iff.mp hz2,
      sq_eq_zero_iff.mp hx2,
      sq_eq_zero_iff.mp hy2⟩
  exact (QuadraticForm.forall_quaternary_normForm_eq_zero_iff_forall_ternary_eq_zero ℚ
    (-1) (-1) (by norm_num) (by norm_num)).mpr htern
