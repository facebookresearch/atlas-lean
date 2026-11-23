/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Complex.PhragmenLindelofPolynomial

@[expose] public section

open Complex

-- `exactSource` consumer with the original binders.
example (a b α : ℝ) (hab : a < b) (hα : 0 ≤ α) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (f : ℂ → ℂ) (M : ℝ), 0 ≤ M →
        DiffContOnCl ℂ f (Complex.re ⁻¹' Set.Ioo a b) →
        (∃ c : ℝ, c < Real.pi / (b - a) ∧ ∃ B : ℝ, ∀ z : ℂ, a < z.re → z.re < b →
            ‖f z‖ ≤ Real.exp (B * Real.exp (c * |z.im|))) →
        (∀ z : ℂ, z.re = a → ‖f z‖ ≤ M * (1 + |z.im|) ^ α) →
        (∀ z : ℂ, z.re = b → ‖f z‖ ≤ M * (1 + |z.im|) ^ α) →
        ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ‖f z‖ ≤ C * M * (1 + |z.im|) ^ α :=
  PhragmenLindelof.exists_norm_le_mul_one_add_abs_im_rpow_of_vertical_strip a b α hab hα

-- The case `α = 0` recovers a constant interior bound from constant
-- boundary bounds.
example (a b : ℝ) (hab : a < b) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (f : ℂ → ℂ) (M : ℝ), 0 ≤ M →
        DiffContOnCl ℂ f (Complex.re ⁻¹' Set.Ioo a b) →
        (∃ c : ℝ, c < Real.pi / (b - a) ∧ ∃ B : ℝ, ∀ z : ℂ, a < z.re → z.re < b →
            ‖f z‖ ≤ Real.exp (B * Real.exp (c * |z.im|))) →
        (∀ z : ℂ, z.re = a → ‖f z‖ ≤ M * (1 + |z.im|) ^ (0 : ℝ)) →
        (∀ z : ℂ, z.re = b → ‖f z‖ ≤ M * (1 + |z.im|) ^ (0 : ℝ)) →
        ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ‖f z‖ ≤ C * M * (1 + |z.im|) ^ (0 : ℝ) :=
  PhragmenLindelof.exists_norm_le_mul_one_add_abs_im_rpow_of_vertical_strip a b 0 hab le_rfl

-- The boundary hypothesis cannot be dropped: for the constant function
-- `1` and `M = 0`, the asserted interior bound at `0` would read `1 ≤ 0`.
example (C : ℝ) : ¬ ‖(1 : ℂ)‖ ≤ C * 0 * (1 + |(0 : ℂ).im|) ^ (0 : ℝ) := by
  simp
