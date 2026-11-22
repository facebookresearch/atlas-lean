/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.AnodyneTesting
public import MathlibExt.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalAnodyneSystem

/-!
# AnodyneTesting

Public consumers of anodyne homotopy testing for the actual finite-J system.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra

universe u

namespace SSet.joyalInterval.AnodyneTestingTest

variable {X Y T : SSet.{u}}

/-- The returned prism keeps the given whole source prism and both endpoint maps. -/
theorem wholePrismExtension (i : X ⟶ Y) (hi : auxiliaryAnodyneExtensions i)
    (hT : auxiliaryAnodyneExtensions.naiveFibrantObjects T) (a₀ a₁ : Y ⟶ T)
    (H : (productPrecylinder.app X).LeftHomotopy (i ≫ a₀) (i ≫ a₁)) :
    ∃ F : productPrecylinder.I.obj Y ⟶ T,
      productPrecylinder.I.map i ≫ F = H.h ∧
      (productPrecylinder.app Y).i₀ ≫ F = a₀ ∧
      (productPrecylinder.app Y).i₁ ≫ F = a₁ := by
  obtain ⟨K, hK⟩ := Precylinder.IsAnodyneSystem.extendLeftHomotopy_of_anodyne
    productPrecylinder auxiliaryAnodyneExtensions i hi hT a₀ a₁ H
  exact ⟨K.h, hK, K.h₀, K.h₁⟩

/-- An arbitrary quotient class lifts; the input is not assumed to be a chosen map. -/
theorem liftClass (i : X ⟶ Y) (hi : auxiliaryAnodyneExtensions i)
    (hT : auxiliaryAnodyneExtensions.naiveFibrantObjects T)
    (c : productPrecylinder.HomotopyClass X T) :
    ∃ d : productPrecylinder.HomotopyClass Y T,
      productPrecylinder.homotopyClassPrecomp i T d = c :=
  (Precylinder.IsAnodyneSystem.bijective_homotopyClassPrecomp_of_anodyne
    productPrecylinder auxiliaryAnodyneExtensions i hi hT).surjective c

/-- Equality after actual class precomposition determines the original classes. -/
theorem identifyClasses (i : X ⟶ Y) (hi : auxiliaryAnodyneExtensions i)
    (hT : auxiliaryAnodyneExtensions.naiveFibrantObjects T)
    (c₀ c₁ : productPrecylinder.HomotopyClass Y T)
    (hc : productPrecylinder.homotopyClassPrecomp i T c₀ =
      productPrecylinder.homotopyClassPrecomp i T c₁) : c₀ = c₁ :=
  (Precylinder.IsAnodyneSystem.bijective_homotopyClassPrecomp_of_anodyne
    productPrecylinder auxiliaryAnodyneExtensions i hi hT).injective hc

/-- Every actual auxiliary anodyne map satisfies the complete finite-J testing predicate. -/
theorem auxiliaryWeak (i : X ⟶ Y) (hi : auxiliaryAnodyneExtensions i) :
    productPrecylinder.testingEquivalences auxiliaryAnodyneExtensions i :=
  Precylinder.IsAnodyneSystem.anodyne_le_testingEquivalences
    productPrecylinder auxiliaryAnodyneExtensions i hi

end SSet.joyalInterval.AnodyneTestingTest
