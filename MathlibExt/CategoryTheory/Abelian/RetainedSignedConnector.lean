/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module
public import MathlibExt.CategoryTheory.Abelian.RightDerived.SignedBoundaryCompatibility

/-!
## Original connector comparison under the retained adjacent-degree normalization
-/
@[expose] public section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Preadditive

namespace CategoryTheory.ProjectiveResolution
variable {C : Type u} [Category.{v} C] [Preadditive C]

/--
A true original connector comparison remains the original adjacent-degree cross-sign equation
after applying the retained normalization to its maps.
-/
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
