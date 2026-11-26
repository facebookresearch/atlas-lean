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
# Identity and composition of small étale sheaf images

For coefficients in universe `max u w`, direct image along the identity is isomorphic to the
identity functor, and successive direct images `f_*` then `g_*` are isomorphic to `(f ≫ g)_*`.

Adjunction mates give the corresponding inverse-image comparisons: the identity inverse image
is the identity, and `g^*` followed by `f^*` is isomorphic to `(f ≫ g)^*`. These comparisons
are natural in sheaf morphisms.

See Milne, Lectures on Étale Cohomology, §8, pp. 60–61.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
universe u w

namespace AlgebraicGeometry.Scheme.DerivedSections

/-- Direct image along the identity is the identity functor.

Base-change identity gives a natural isomorphism from the direct image of the identity scheme
map to the identity sheaf functor. -/
def smallEtaleDirectImageIdIso (X : Scheme.{u}) :
    smallEtaleDirectImage.{u, max u w} (𝟙 X) ≅
      𝟭 (Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) := by
  let : (smallEtaleBaseChange (𝟙 X)).IsContinuous X.smallEtaleTopology X.smallEtaleTopology :=
    smallEtaleBaseChange_isContinuous (𝟙 X)
  exact Functor.sheafPushforwardContinuousId' (smallEtaleBaseChangeId X)
    AddCommGrpCat.{max u w} X.smallEtaleTopology

/-- Successive direct images equal the composite direct image naturally.

For `f : X → Y` and `g : Y → Z`, there is a natural isomorphism `f_* ⋙ g_* ≅ (f ≫ g)_*`. -/
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

/-- Inverse image along the identity is the identity functor.

The identity direct-image comparison and adjunction give a natural isomorphism from identity
inverse image to the identity sheaf functor. -/
def smallEtaleInverseImageIdIso (X : Scheme.{u}) :
    smallEtaleInverseImage.{u, w} (𝟙 X) ≅
      𝟭 (Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) :=
  Adjunction.leftAdjointIdIso (smallEtaleInverseImageAdjunction.{u, w} (𝟙 X))
    (smallEtaleDirectImageIdIso.{u, w} X)

/-- Successive inverse images equal the composite inverse image naturally.

For composable scheme maps, the adjunction mate gives `g^* ⋙ f^* ≅ (f ≫ g)^*`. -/
def smallEtaleInverseImageCompIso {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    smallEtaleInverseImage.{u, w} g ⋙ smallEtaleInverseImage.{u, w} f ≅
      smallEtaleInverseImage.{u, w} (f ≫ g) :=
  Adjunction.leftAdjointCompIso (smallEtaleInverseImageAdjunction.{u, w} g)
    (smallEtaleInverseImageAdjunction.{u, w} f)
    (smallEtaleInverseImageAdjunction.{u, w} (f ≫ g))
    (smallEtaleDirectImageCompIso.{u, w} f g)

/-- Identity inverse image comparison mates to inverse direct image comparison.

The forward inverse-image identity comparison corresponds under the adjunction conjugation
equivalence to the inverse direct-image identity comparison. -/
theorem smallEtaleInverseImageIdIso_mate (X : Scheme.{u}) :
    conjugateEquiv (Adjunction.id (C := Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}))
        (smallEtaleInverseImageAdjunction.{u, w} (𝟙 X))
        (smallEtaleInverseImageIdIso.{u, w} X).hom =
      (smallEtaleDirectImageIdIso.{u, w} X).inv := by
  exact Adjunction.conjugateEquiv_leftAdjointIdIso_hom
    (smallEtaleInverseImageAdjunction.{u, w} (𝟙 X)) (smallEtaleDirectImageIdIso.{u, w} X)

/-- Inverse composition comparison mates to forward direct image comparison.

The inverse of the inverse-image composition isomorphism corresponds under the two adjunctions
to the forward direct-image composition isomorphism. -/
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

/-- Direct image identity comparison is natural in sheaf maps.

The identity direct-image comparison commutes with every sheaf morphism. -/
theorem smallEtaleDirectImageIdIso_naturality (X : Scheme.{u})
    {Q Q' : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}} (τ : Q ⟶ Q') :
    (smallEtaleDirectImage.{u, max u w} (𝟙 X)).map τ ≫
        (smallEtaleDirectImageIdIso.{u, w} X).hom.app Q' =
      (smallEtaleDirectImageIdIso.{u, w} X).hom.app Q ≫ τ := by
  exact (smallEtaleDirectImageIdIso.{u, w} X).hom.naturality τ

/-- Direct image composition comparison is natural in sheaf maps.

A sheaf morphism commutes with the comparison from successive direct images to direct image
along the composite. -/
theorem smallEtaleDirectImageCompIso_naturality
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    {Q Q' : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}} (τ : Q ⟶ Q') :
    (smallEtaleDirectImage.{u, max u w} f ⋙ smallEtaleDirectImage.{u, max u w} g).map τ ≫
        (smallEtaleDirectImageCompIso.{u, w} f g).hom.app Q' =
      (smallEtaleDirectImageCompIso.{u, w} f g).hom.app Q ≫
        (smallEtaleDirectImage.{u, max u w} (f ≫ g)).map τ := by
  exact (smallEtaleDirectImageCompIso.{u, w} f g).hom.naturality τ

/-- Inverse image identity comparison is natural in sheaf maps.

The identity inverse-image comparison commutes with every sheaf morphism. -/
theorem smallEtaleInverseImageIdIso_naturality (X : Scheme.{u})
    {Q Q' : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}} (τ : Q ⟶ Q') :
    (smallEtaleInverseImage.{u, w} (𝟙 X)).map τ ≫
        (smallEtaleInverseImageIdIso.{u, w} X).hom.app Q' =
      (smallEtaleInverseImageIdIso.{u, w} X).hom.app Q ≫ τ := by
  exact (smallEtaleInverseImageIdIso.{u, w} X).hom.naturality τ

/-- Inverse image composition comparison is natural in sheaf maps.

A sheaf morphism commutes with the comparison from successive inverse images to inverse image
along the composite. -/
theorem smallEtaleInverseImageCompIso_naturality
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    {Q Q' : Sheaf Z.smallEtaleTopology AddCommGrpCat.{max u w}} (τ : Q ⟶ Q') :
    (smallEtaleInverseImage.{u, w} g ⋙ smallEtaleInverseImage.{u, w} f).map τ ≫
        (smallEtaleInverseImageCompIso.{u, w} f g).hom.app Q' =
      (smallEtaleInverseImageCompIso.{u, w} f g).hom.app Q ≫
        (smallEtaleInverseImage.{u, w} (f ≫ g)).map τ := by
  exact (smallEtaleInverseImageCompIso.{u, w} f g).hom.naturality τ

end AlgebraicGeometry.Scheme.DerivedSections
