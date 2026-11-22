/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.ModelCategory.HomotopyTestingRelativeDeformation
public import MathlibExt.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalAnodyneSystem
public import MathlibExt.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalFactorization

/-!
# Public consumers of the full relative deformation criterion
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

universe w v u

namespace MathlibExtTest.AlgebraicTopology.ModelCategory.HomotopyTestingRelativeDeformation

section Generic

variable {C : Type u} [Category.{v} C] [HasBinaryCoproducts C] [HasPushouts C]
  [HasInitial C] [InitialMonoClass C] [HasTerminal C]
  (P : Precylinder (𝟭 C)) [P.IsExact.{w}]
  (An : MorphismProperty C) [P.IsAnodyneSystem.{w} An]
  [MorphismProperty.HasFactorization An An.rlp]

/-- The public iff gives the actual retraction and homotopy, including
both endpoints and stationarity on the entire original source cylinder. -/
theorem deformationOfTesting {X Y : C} (i : X ⟶ Y) [Mono i]
    (hX : An.naiveFibrantObjects X) (hY : An.naiveFibrantObjects Y)
    (hi : P.testingEquivalences An i) :
    ∃ (r : Y ⟶ X) (H : P.I.obj Y ⟶ Y),
      i ≫ r = 𝟙 X ∧ (P.app Y).i₀ ≫ H = 𝟙 Y ∧
        (P.app Y).i₁ ≫ H = r ≫ i ∧ P.I.map i ≫ H = (P.app X).π ≫ i := by
  obtain ⟨D⟩ :=
    (Precylinder.IsAnodyneSystem.testingEquivalences_iff_nonempty_strongDeformationData_of_mono
      P An i hX hY).mp hi
  exact ⟨D.retraction, D.homotopy.h, D.retract, D.homotopy.h₀, D.homotopy.h₁, D.stationary⟩

end Generic

open SSet SSet.joyalInterval

local instance : MorphismProperty.HasFactorization auxiliaryAnodyneExtensions.{u}
    auxiliaryAnodyneExtensions.rlp := by
  change MorphismProperty.HasFactorization auxiliaryAnodyneExtensions.{u}
    auxiliaryNaiveFibrations.{u}
  infer_instance

/-- Actual finite-J deformation data supply the reverse direction of the
public testing iff, with the original monomorphism and both naive objects. -/
theorem finiteJTestingOfData {X Y : SSet.{u}} (i : X ⟶ Y) [Mono i]
    (hX : auxiliaryNaiveFibrantObjects X) (hY : auxiliaryNaiveFibrantObjects Y)
    (D : productPrecylinder.StrongDeformationData i) :
    productPrecylinder.testingEquivalences auxiliaryAnodyneExtensions i :=
  (Precylinder.IsAnodyneSystem.testingEquivalences_iff_nonempty_strongDeformationData_of_mono
    productPrecylinder auxiliaryAnodyneExtensions i hX hY).mpr ⟨D⟩

/-- The full TFAE supplies anodyneness to the existing chosen-retraction
extension, retaining that exact retraction and every full homotopy equation. -/
theorem finiteJChosenRetraction {X Y : SSet.{u}} (i : X ⟶ Y) [Mono i]
    (hX : auxiliaryNaiveFibrantObjects X) (hY : auxiliaryNaiveFibrantObjects Y)
    (hi : productPrecylinder.testingEquivalences auxiliaryAnodyneExtensions i)
    (r : Y ⟶ X) (hr : i ≫ r = 𝟙 X) :
    ∃ D : productPrecylinder.StrongDeformationData i,
      D.retraction = r ∧ i ≫ r = 𝟙 X ∧
        (productPrecylinder.app Y).i₀ ≫ D.homotopy.h = 𝟙 Y ∧
        (productPrecylinder.app Y).i₁ ≫ D.homotopy.h = r ≫ i ∧
        productPrecylinder.I.map i ≫ D.homotopy.h = (productPrecylinder.app X).π ≫ i := by
  have hAn : auxiliaryAnodyneExtensions i :=
    ((Precylinder.IsAnodyneSystem.testingEquivalences_anodyne_strongDeformationData_tfae
      productPrecylinder auxiliaryAnodyneExtensions i hX hY).out 1 2).mp hi
  obtain ⟨D, hD⟩ := Precylinder.IsAnodyneSystem.exists_strongDeformationData_of_anodyne_retraction
    productPrecylinder auxiliaryAnodyneExtensions i hAn hY r hr
  refine ⟨D, hD, ?_, D.homotopy.h₀, ?_, D.stationary⟩
  · simpa only [hD] using D.retract
  · simpa only [hD] using D.homotopy.h₁

end MathlibExtTest.AlgebraicTopology.ModelCategory.HomotopyTestingRelativeDeformation
