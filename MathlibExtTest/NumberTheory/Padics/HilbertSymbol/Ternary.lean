/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Padics.HilbertSymbol.Ternary

/-! # Tests for `MathlibExt.NumberTheory.Padics.HilbertSymbol.Ternary` -/

namespace MathlibExtTest.HilbertSymbolTernary

-- `x² + y² + z²` has no nonzero real zero, so `(-1, -1)_ℝ ≠ 1`.
example : hilbertSymbol ℝ (-1) (-1) ≠ 1 := by
  intro h
  obtain ⟨x, y, z, hne, h0⟩ :=
    (hilbertSymbol.exists_ternary_eq_zero_iff two_ne_zero 1 1 1).2 (by simpa using h)
  simp only [Units.val_one, one_mul] at h0
  have hx : x = 0 := by nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
  have hy : y = 0 := by nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
  have hz : z = 0 := by nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
  exact hne ⟨hx, hy, hz⟩

-- `x² + y² = 2` has the solution `(1, 1)`, so `(2, -1)_p = (1, 1)_p = 1` for every prime `p`.
example (p : ℕ) [Fact p.Prime] : padicHilbertSymbol p (Units.mk0 2 two_ne_zero) (-1) = 1 := by
  have h := (padicHilbertSymbol.exists_mul_sq_add_mul_sq_eq_iff (p := p) 1 1
    (Units.mk0 2 two_ne_zero)).1 ⟨1, 1, by norm_num⟩
  rw [mul_one] at h
  rw [← h, padicHilbertSymbol.eq_one_iff]
  exact ⟨1, 0, by norm_num⟩

-- `x² - y² + c z²` has the zero `(1, 1, 0)`, so `(1, -1)_p = (-c, 1)_p` for every `c`.
example (p : ℕ) [Fact p.Prime] (c : ℚ_[p]ˣ) :
    padicHilbertSymbol p 1 (-1) = padicHilbertSymbol p (-c) (-(1 * -1)) :=
  (padicHilbertSymbol.exists_ternary_eq_zero_iff 1 (-1) c).1
    ⟨1, 1, 0, fun h => one_ne_zero h.1, by simp⟩

-- The anisotropic form `x² + y² + z²` over `ℝ` does not take the value `-1`, as `1` is a square.
example : ¬∃ x y z : ℝ, x ^ 2 + y ^ 2 + z ^ 2 = -1 := by
  have hf : ¬∃ x₁ x₂ x₃ : ℝ, ¬(x₁ = 0 ∧ x₂ = 0 ∧ x₃ = 0) ∧
      ((1 : ℝˣ) : ℝ) * x₁ ^ 2 + ((1 : ℝˣ) : ℝ) * x₂ ^ 2 + ((1 : ℝˣ) : ℝ) * x₃ ^ 2 = 0 := by
    rintro ⟨x, y, z, hne, h0⟩
    simp only [Units.val_one, one_mul] at h0
    have hx : x = 0 := by nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
    have hy : y = 0 := by nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
    have hz : z = 0 := by nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
    exact hne ⟨hx, hy, hz⟩
  have h := realHilbertSymbol.exists_ternary_eq_iff_not_isSquare 1 1 1 (-1) hf
  simp only [Units.val_one, one_mul, Units.val_neg, neg_neg, mul_one] at h
  rw [h]
  exact fun h' => h' ⟨1, by norm_num⟩

-- The isotropic form `x² + y² - z²` over `ℝ` takes every nonzero value, `-5` included.
example : ∃ x y z : ℝ, x ^ 2 + y ^ 2 - z ^ 2 = -5 := by
  have h := ((realHilbertSymbol.ternary_criteria 1 1 (-1)).2 (Units.mk0 (-5) (by norm_num))).2
    (Or.inl ⟨1, 0, 1, fun h => one_ne_zero h.1, by simp⟩)
  obtain ⟨x, y, z, hxyz⟩ := h
  exact ⟨x, y, z, by simpa [sub_eq_add_neg] using hxyz⟩

end MathlibExtTest.HilbertSymbolTernary
