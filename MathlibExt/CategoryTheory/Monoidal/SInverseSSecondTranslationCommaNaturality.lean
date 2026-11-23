/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.RightCommaBousfieldKan
public import
  MathlibExt.CategoryTheory.Monoidal.SInverseSSecondTranslationComma

/-!
# Base naturality of second-coordinate right-comma translation

Second-coordinate translation commutes with every base-change functor between
right-comma categories.  We first construct the identity-left-component
naturality isomorphism, turn it into a proof-cast-stable strict functor
equality, and then package the corresponding endomorphisms of the right-comma
nerve diagram and its precomposition by first-coordinate base translation.

This file makes no homology, module, localization, or coefficient-action
claim.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits ZeroObject

universe v u

namespace CategoryTheory
namespace SInverseS

section General

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  [HasZeroObject C] [HasBinaryBiproducts C]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Second-coordinate translation commutes, up to its canonical
identity-left-component isomorphism, with right-comma base change. -/
noncomputable def secondTranslationCostructuredMapNaturalityIso
    (A : C) {B D : Translation C} (g : B ⟶ D) :
    CostructuredArrow.map g ⋙ secondTranslationCostructuredMap A D ≅
      secondTranslationCostructuredMap A B ⋙ CostructuredArrow.map g :=
  NatIso.ofComponents
    (fun X => CostructuredArrow.isoMk (Iso.refl _) (by
      simp [secondTranslationCostructuredMap,
        secondTranslationProjectionNatTrans, CostructuredArrow.map]))
    (by
      intro X Y f
      apply CostructuredArrow.ext
      simp [Functor.comp_map, secondTranslationCostructuredMap,
        secondTranslationProjectionNatTrans, CostructuredArrow.map])

@[simp]
theorem secondTranslationCostructuredMapNaturalityIso_hom_app_left
    (A : C) {B D : Translation C} (g : B ⟶ D)
    (X : CostructuredArrow (translationProjection (C := C)) B) :
    ((secondTranslationCostructuredMapNaturalityIso A g).hom.app X).left =
      𝟙 _ := by
  change (Iso.refl _).hom = 𝟙 _
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Equality of the two second-translated comma objects associated to a base
arrow. -/
theorem secondTranslationCostructuredMapNaturalityObjEq
    (A : C) {B D : Translation C} (g : B ⟶ D)
    (X : CostructuredArrow (translationProjection (C := C)) B) :
    (CostructuredArrow.map g ⋙
        secondTranslationCostructuredMap A D).obj X =
      (secondTranslationCostructuredMap A B ⋙
        CostructuredArrow.map g).obj X := by
  let hleft :
      ((CostructuredArrow.map g ⋙
          secondTranslationCostructuredMap A D).obj X).left =
        ((secondTranslationCostructuredMap A B ⋙
          CostructuredArrow.map g).obj X).left := by
    simp only [Functor.comp_obj, CostructuredArrow.map_obj_left,
      secondTranslationCostructuredMap_obj_left]
  apply CostructuredArrow.obj_ext _ _ hleft
  rw [show hleft = rfl from Subsingleton.elim _ _]
  simp [Functor.comp_obj, secondTranslationCostructuredMap,
    secondTranslationProjectionNatTrans, CostructuredArrow.map]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The naturality-isomorphism component is transport along the named
comma-object equality. -/
theorem secondTranslationCostructuredMapNaturalityIso_hom_app_eqToHom
    (A : C) {B D : Translation C} (g : B ⟶ D)
    (X : CostructuredArrow (translationProjection (C := C)) B) :
    (secondTranslationCostructuredMapNaturalityIso A g).hom.app X =
      eqToHom (secondTranslationCostructuredMapNaturalityObjEq A g X) := by
  apply CostructuredArrow.ext
  simp [secondTranslationCostructuredMapNaturalityIso]

/-- Strict base naturality of fiberwise second-coordinate right-comma
translation. -/
theorem secondTranslationCostructuredMap_naturality
    (A : C) {B D : Translation C} (g : B ⟶ D) :
    CostructuredArrow.map g ⋙ secondTranslationCostructuredMap A D =
      secondTranslationCostructuredMap A B ⋙ CostructuredArrow.map g :=
  Functor.ext_of_iso (secondTranslationCostructuredMapNaturalityIso A g)
    (secondTranslationCostructuredMapNaturalityObjEq A g)
    (secondTranslationCostructuredMapNaturalityIso_hom_app_eqToHom A g)

end General

section SmallUniverse

variable {C₀ : Type u} [Category.{u} C₀] [HasZeroMorphisms C₀]
  [HasZeroObject C₀] [HasBinaryBiproducts C₀]

/-- Second-coordinate translation is a base-natural endomorphism of the
right-comma nerve diagram. -/
noncomputable def secondTranslationRightCommaNerveDiagramNatTrans (A : C₀) :
    SSet.rightCommaNerveDiagram (translationProjection (C := C₀)) ⟶
      SSet.rightCommaNerveDiagram (translationProjection (C := C₀)) where
  app B := nerveMap (secondTranslationCostructuredMap A B)
  naturality {B D} g := by
    change
      nerveMap (CostructuredArrow.map g) ≫
          nerveMap (secondTranslationCostructuredMap A D) =
        nerveMap (secondTranslationCostructuredMap A B) ≫
          nerveMap (CostructuredArrow.map g)
    rw [nerveMap_comp, nerveMap_comp,
      secondTranslationCostructuredMap_naturality]

@[simp]
theorem secondTranslationRightCommaNerveDiagramNatTrans_app
    (A : C₀) (B : Translation C₀) :
    (secondTranslationRightCommaNerveDiagramNatTrans A).app B =
      nerveMap (secondTranslationCostructuredMap A B) :=
  rfl

/-- The second-translation endomorphism of the right-comma nerve diagram,
prewhiskered by first-coordinate base translation. -/
noncomputable def secondTranslationTranslatedRightCommaNerveDiagramNatTrans
    (A : C₀) :
    Translation.translateFunctor A ⋙
        SSet.rightCommaNerveDiagram (translationProjection (C := C₀)) ⟶
      Translation.translateFunctor A ⋙
        SSet.rightCommaNerveDiagram (translationProjection (C := C₀)) :=
  Functor.whiskerLeft (Translation.translateFunctor A)
    (secondTranslationRightCommaNerveDiagramNatTrans A)

@[simp]
theorem secondTranslationTranslatedRightCommaNerveDiagramNatTrans_app
    (A : C₀) (B : Translation C₀) :
    (secondTranslationTranslatedRightCommaNerveDiagramNatTrans A).app B =
      nerveMap (secondTranslationCostructuredMap A
        ((Translation.translateFunctor A).obj B)) :=
  rfl

end SmallUniverse

end SInverseS
end CategoryTheory

end
