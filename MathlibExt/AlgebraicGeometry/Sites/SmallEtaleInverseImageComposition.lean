/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Authors: @toskua, Avocado
module
public import MathlibExt.AlgebraicGeometry.Sites.SmallEtaleInverseImage
public import Mathlib.CategoryTheory.Adjunction.CompositionIso

/-!
# Identity and composition comparisons on étale sites

Direct-image comparisons use base-change identity and composition
comparisons. Inverse-image comparisons follow from the adjunctions and
uniqueness of adjoints. Milne, §8, pp. 60–61.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
universe u w

namespace AlgebraicGeometry.Scheme.DerivedSections

/-- The actual identity direct image identifies canonically with the identity functor. -/
def smallEtaleDirectImageIdIso (X : Scheme.{u}) :
    smallEtaleDirectImage.{u, max u w} (𝟙 X) ≅
      𝟭 (Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) := by
  let : (smallEtaleBaseChange (𝟙 X)).IsContinuous X.smallEtaleTopology X.smallEtaleTopology :=
    smallEtaleBaseChange_isContinuous (𝟙 X)
  exact Functor.sheafPushforwardContinuousId' (smallEtaleBaseChangeId X)
    AddCommGrpCat.{max u w} X.smallEtaleTopology

/-- The actual direct images compose via the same canonical fiber-product comparison. -/
def smallEtaleDirectImageCompIso {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    smallEtaleDirectImage.{u, max u w} f ⋙ smallEtaleDirectImage.{u, max u w} g ≅
      smallEtaleDirectImage.{u, max u w} (f ≫ g) := by
  let : (smallEtaleBaseChange f).IsContinuous Y.smallEtaleTopology X.smallEtaleTopology :=
    smallEtaleBaseChange_isContinuous f
  let : (smallEtaleBaseChange g).IsContinuous Z.smallEtaleTopology Y.smallEtaleTopology :=
    smallEtaleBaseChange_isContinuous g
  let : (smallEtaleBaseChange (f ≫ g)).IsContinuous Z.smallEtaleTopology X.smallEtaleTopology :=
    smallEtaleBaseChange_isContinuous (f ≫ g)
  exact Functor.sheafPushforwardContinuousComp' (smallEtaleBaseChangeComp f g).symm
    AddCommGrpCat.{max u w} Z.smallEtaleTopology Y.smallEtaleTopology X.smallEtaleTopology

/-- The actual identity inverse image is the adjunction mate of the same direct-image identity. -/
def smallEtaleInverseImageIdIso (X : Scheme.{u}) :
    smallEtaleInverseImage.{u, w} (𝟙 X) ≅
      𝟭 (Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) :=
  Adjunction.leftAdjointIdIso (smallEtaleInverseImageAdjunction.{u, w} (𝟙 X))
    (smallEtaleDirectImageIdIso.{u, w} X)

/-- The actual composite inverse image is canonically the inverse image of
the original composite, through its concrete direct-image adjunction mate. -/
def smallEtaleInverseImageCompIso {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    smallEtaleInverseImage.{u, w} g ⋙ smallEtaleInverseImage.{u, w} f ≅
      smallEtaleInverseImage.{u, w} (f ≫ g) :=
  Adjunction.leftAdjointCompIso (smallEtaleInverseImageAdjunction.{u, w} g)
    (smallEtaleInverseImageAdjunction.{u, w} f)
    (smallEtaleInverseImageAdjunction.{u, w} (f ≫ g))
    (smallEtaleDirectImageCompIso.{u, w} f g)

/-- The identity comparison is the mate of the very same original direct-image identity. -/
theorem smallEtaleInverseImageIdIso_mate (X : Scheme.{u}) :
    conjugateEquiv (Adjunction.id (C := Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}))
        (smallEtaleInverseImageAdjunction.{u, w} (𝟙 X))
        (smallEtaleInverseImageIdIso.{u, w} X).hom =
      (smallEtaleDirectImageIdIso.{u, w} X).inv := by
  exact Adjunction.conjugateEquiv_leftAdjointIdIso_hom
    (smallEtaleInverseImageAdjunction.{u, w} (𝟙 X)) (smallEtaleDirectImageIdIso.{u, w} X)

/-- The composition comparison intertwines the fixed actual adjunctions:
its inverse has the prescribed original direct-image composition as mate. -/
theorem smallEtaleInverseImageCompIso_mate
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    conjugateEquiv
        ((smallEtaleInverseImageAdjunction.{u, w} g).comp
          (smallEtaleInverseImageAdjunction.{u, w} f))
        (smallEtaleInverseImageAdjunction.{u, w} (f ≫ g))
        (smallEtaleInverseImageCompIso.{u, w} f g).inv =
      (smallEtaleDirectImageCompIso.{u, w} f g).hom := by
  exact Adjunction.conjugateEquiv_leftAdjointCompIso_inv
    (smallEtaleInverseImageAdjunction.{u, w} g)
    (smallEtaleInverseImageAdjunction.{u, w} f)
    (smallEtaleInverseImageAdjunction.{u, w} (f ≫ g))
    (smallEtaleDirectImageCompIso.{u, w} f g)

/-- Identity direct-image comparison preserves every original sheaf morphism. -/
theorem smallEtaleDirectImageIdIso_naturality (X : Scheme.{u})
    {Q Q' : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}} (τ : Q ⟶ Q') :
    (smallEtaleDirectImage.{u, max u w} (𝟙 X)).map τ ≫
        (smallEtaleDirectImageIdIso.{u, w} X).hom.app Q' =
      (smallEtaleDirectImageIdIso.{u, w} X).hom.app Q ≫ τ := by
  exact (smallEtaleDirectImageIdIso.{u, w} X).hom.naturality τ

/-- Composite direct-image comparison preserves every original sheaf morphism. -/
theorem smallEtaleDirectImageCompIso_naturality
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    {Q Q' : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}} (τ : Q ⟶ Q') :
    (smallEtaleDirectImage.{u, max u w} f ⋙ smallEtaleDirectImage.{u, max u w} g).map τ ≫
        (smallEtaleDirectImageCompIso.{u, w} f g).hom.app Q' =
      (smallEtaleDirectImageCompIso.{u, w} f g).hom.app Q ≫
        (smallEtaleDirectImage.{u, max u w} (f ≫ g)).map τ := by
  exact (smallEtaleDirectImageCompIso.{u, w} f g).hom.naturality τ

/-- Identity inverse-image comparison preserves every original sheaf morphism. -/
theorem smallEtaleInverseImageIdIso_naturality (X : Scheme.{u})
    {Q Q' : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}} (τ : Q ⟶ Q') :
    (smallEtaleInverseImage.{u, w} (𝟙 X)).map τ ≫
        (smallEtaleInverseImageIdIso.{u, w} X).hom.app Q' =
      (smallEtaleInverseImageIdIso.{u, w} X).hom.app Q ≫ τ := by
  exact (smallEtaleInverseImageIdIso.{u, w} X).hom.naturality τ

/-- Composite inverse-image comparison preserves every original sheaf morphism. -/
theorem smallEtaleInverseImageCompIso_naturality
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    {Q Q' : Sheaf Z.smallEtaleTopology AddCommGrpCat.{max u w}} (τ : Q ⟶ Q') :
    (smallEtaleInverseImage.{u, w} g ⋙ smallEtaleInverseImage.{u, w} f).map τ ≫
        (smallEtaleInverseImageCompIso.{u, w} f g).hom.app Q' =
      (smallEtaleInverseImageCompIso.{u, w} f g).hom.app Q ≫
        (smallEtaleInverseImage.{u, w} (f ≫ g)).map τ := by
  exact (smallEtaleInverseImageCompIso.{u, w} f g).hom.naturality τ

end AlgebraicGeometry.Scheme.DerivedSections
