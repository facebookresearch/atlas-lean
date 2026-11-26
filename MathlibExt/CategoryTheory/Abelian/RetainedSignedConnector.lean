/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module
public import MathlibExt.CategoryTheory.Abelian.RightDerived.SignedBoundaryCompatibility

/- Proof implementation note.
## Original connector comparison under the retained adjacent-degree normalization
-/

/-!
# Connecting squares under triangular normalization

In a preadditive category, a commutative connecting square remains
commutative after triangular normalization with the adjacent-degree
factor `(-1)^(n+1)`.
-/
@[expose] public section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Preadditive

namespace CategoryTheory.ProjectiveResolution
variable {C : Type u} [Category.{v} C] [Preadditive C]

/- Proof implementation note.
A true original connector comparison remains the original adjacent-degree cross-sign equation
after applying the retained normalization to its maps.
-/

/-- In a preadditive category `C`, let `δ : A → B`, `δ′ : A′ → B′`
and `e₀ : A → A′`, `e₁ : B → B′` satisfy `δ ≫ e₁=e₀ ≫ δ′`.
For `σ_n=(-1)^(n(n+1)/2)`, normalization gives
`δ ≫ (σ_(n+1) • e₁) = (-1)^(n+1) • ((σ_n • e₀) ≫ δ′)`. -/
theorem retainedSignedConnector {A B A' B' : C}
    (δ : A ⟶ B) (δ' : A' ⟶ B') (e₀ : A ⟶ A') (e₁ : B ⟶ B')
    (n : ℕ) (h : δ ≫ e₁ = e₀ ≫ δ') :
    δ ≫ (acyclicResolutionNormalizationSign (n + 1) • e₁) =
      (-1 : ℤ) ^ (n + 1) • ((acyclicResolutionNormalizationSign n • e₀) ≫ δ') := by
  rw [comp_zsmul, zsmul_comp, smul_smul]
  change acyclicResolutionNormalizationSign (n + 1) • (δ ≫ e₁) =
    (normalizationCrossSign n * acyclicResolutionNormalizationSign n) • (e₀ ≫ δ')
  rw [h]
  rfl

end CategoryTheory.ProjectiveResolution
