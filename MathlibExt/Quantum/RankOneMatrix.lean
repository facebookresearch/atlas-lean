/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Complex.Basic
public import Mathlib.Algebra.Field.Basic

/-!
# Rank-one coefficient matrices

A complex matrix in product form is exactly a matrix whose
`2 × 2` minors all vanish. This is the rank-one case used
for Schmidt coefficients; higher-rank decomposition is not
included here.
-/

@[expose] public section

/-- Schmidt rank-one characterization, coefficient-matrix
form (core of QCI-13): a matrix `M : Fin m → Fin n → ℂ`
is a product (rank at most one) iff all its `2 × 2` minors
vanish. The forward direction is algebra; the reverse
picks a nonzero entry and factors through it (zero matrix
included via the zero factors). -/
theorem product_iff_minors {m n : ℕ} (M : Fin m → Fin n → ℂ) :
    (∃ a : Fin m → ℂ, ∃ b : Fin n → ℂ, ∀ i j, M i j = a i * b j)
    ↔ ∀ i₁ i₂ j₁ j₂, M i₁ j₁ * M i₂ j₂ = M i₁ j₂ * M i₂ j₁ := by
  constructor
  · rintro ⟨a, b, hab⟩ i₁ i₂ j₁ j₂
    rw [hab, hab, hab, hab]
    ring
  · intro hmin
    by_cases h : ∀ i j, M i j = 0
    · exact ⟨fun _ => 0, fun _ => 0, fun i j => by simp [h i j]⟩
    · push Not at h
      obtain ⟨i₀, j₀, hne⟩ := h
      refine ⟨fun i => M i j₀, fun j => M i₀ j / M i₀ j₀, fun i j => ?_⟩
      have hkey : M i j * M i₀ j₀ = M i j₀ * M i₀ j := hmin i i₀ j j₀
      have h2 : M i j = M i j₀ * M i₀ j / M i₀ j₀ := by
        rw [eq_div_iff hne]
        exact hkey
      rw [h2, mul_div_assoc]

end
