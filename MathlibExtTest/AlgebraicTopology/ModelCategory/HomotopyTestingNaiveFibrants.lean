/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.HomotopyTestingNaiveFibrants
public import MathlibExt.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalAnodyneSystem

/-!
# Homotopy Testing Naive Fibrants
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

universe w v u

namespace MathlibExtTest.AlgebraicTopology.ModelCategory.HomotopyTestingNaiveFibrants

section Generic

variable {C : Type u} [Category.{v} C] [HasTerminal C]
  (P : Precylinder (𝟭 C)) (An : MorphismProperty C) {X Y : C}

/-- The weak-map criterion gives actual invertibility in the chosen quotient. -/
theorem quotientIsoFromWeak (f : X ⟶ Y) (hX : An.naiveFibrantObjects X)
    (hY : An.naiveFibrantObjects Y) (hf : P.testingEquivalences An f) :
    IsIso (P.homotopyQuotientFunctor.map f) :=
  (P.homotopyEquivalences_iff f).mp
    ((P.testingEquivalences_iff_homotopyEquivalences An f hX hY).mp hf)

/-- Both given homotopies retain the original P and imply actual testing membership. -/
theorem weakFromFixedInverse [HasBinaryCoproducts C] [HasPushouts C]
    [P.IsExact.{w}] [P.IsAnodyneSystem.{w} An]
    (f : X ⟶ Y) (g : Y ⟶ X) (hX : An.naiveFibrantObjects X)
    (hY : An.naiveFibrantObjects Y) (H : (P.app X).LeftHomotopy (𝟙 X) (f ≫ g))
    (K : (P.app Y).LeftHomotopy (𝟙 Y) (g ≫ f)) : P.testingEquivalences An f :=
  (Precylinder.IsAnodyneSystem.testingEquivalences_iff_exists_leftHomotopy_inverse
    P An f hX hY).mpr ⟨g, ⟨H⟩, ⟨K⟩⟩

end Generic

open MonoidalCategory SSet SSet.joyalInterval

/-- The full finite-J specialization returns original maps and all four endpoint equations. -/
theorem finiteJInverseMaps {X Y : SSet.{u}} (f : X ⟶ Y)
    (hX : auxiliaryNaiveFibrantObjects X) (hY : auxiliaryNaiveFibrantObjects Y)
    (hf : productPrecylinder.testingEquivalences auxiliaryAnodyneExtensions f) :
    ∃ (g : Y ⟶ X) (H : joyalInterval ⊗ X ⟶ X) (K : joyalInterval ⊗ Y ⟶ Y),
      (productPrecylinder.app X).i₀ ≫ H = 𝟙 X ∧
        (productPrecylinder.app X).i₁ ≫ H = f ≫ g ∧
        (productPrecylinder.app Y).i₀ ≫ K = 𝟙 Y ∧
        (productPrecylinder.app Y).i₁ ≫ K = g ≫ f := by
  obtain ⟨g, ⟨H⟩, ⟨K⟩⟩ :=
    (Precylinder.IsAnodyneSystem.testingEquivalences_iff_exists_leftHomotopy_inverse
      productPrecylinder auxiliaryAnodyneExtensions f hX hY).mp hf
  exact ⟨g, H.h, K.h, H.h₀, H.h₁, K.h₀, K.h₁⟩

end MathlibExtTest.AlgebraicTopology.ModelCategory.HomotopyTestingNaiveFibrants
