/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.RightCommaBousfieldKan
public import MathlibExt.CategoryTheory.Monoidal.SInverseSTranslationCommaAction

/-!
# The translated right-comma nerve diagram

The translated right-comma functors are natural up to an
identity-left-component isomorphism.  We first turn that isomorphism into a
proof-cast-stable equality of functors, then assemble the corresponding
natural transformation from the right-comma nerve diagram to its
precomposition by base translation.

This is the final simplicial-diagram layer before BK linearization.  No chain,
bicomplex, spectral-sequence, localization, realization, or CGWH map is
constructed here.
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
/-- Equality of the two translated comma objects associated to a base
arrow. -/
theorem translationCostructuredMapNaturalityObjEq
    (A : C) {B D : Translation C} (g : B ⟶ D)
    (X : CostructuredArrow (translationProjection (C := C)) B) :
    (CostructuredArrow.map g ⋙ translationCostructuredMap A D).obj X =
      (translationCostructuredMap A B ⋙
        CostructuredArrow.map
          ((Translation.translateFunctor A).map g)).obj X := by
  let hleft :
      ((CostructuredArrow.map g ⋙
          translationCostructuredMap A D).obj X).left =
        ((translationCostructuredMap A B ⋙
          CostructuredArrow.map
            ((Translation.translateFunctor A).map g)).obj X).left := by
    simp only [Functor.comp_obj, CostructuredArrow.map_obj_left,
      translationCostructuredMap_obj_left]
  apply CostructuredArrow.obj_ext _ _ hleft
  rw [show hleft = rfl from Subsingleton.elim _ _]
  simp [Functor.comp_obj, translationCostructuredMap]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The landed naturality isomorphism component is the equality transport
associated to the named comma-object equality. -/
theorem translationCostructuredMapNaturalityIso_hom_app_eqToHom
    (A : C) {B D : Translation C} (g : B ⟶ D)
    (X : CostructuredArrow (translationProjection (C := C)) B) :
    (translationCostructuredMapNaturalityIso A g).hom.app X =
      eqToHom (translationCostructuredMapNaturalityObjEq A g X) := by
  apply CostructuredArrow.ext
  simp [translationCostructuredMapNaturalityIso]

/-- Strict form of naturality of translated right-comma functors. -/
theorem translationCostructuredMap_naturality
    (A : C) {B D : Translation C} (g : B ⟶ D) :
    CostructuredArrow.map g ⋙ translationCostructuredMap A D =
      translationCostructuredMap A B ⋙
        CostructuredArrow.map
          ((Translation.translateFunctor A).map g) :=
  Functor.ext_of_iso (translationCostructuredMapNaturalityIso A g)
    (translationCostructuredMapNaturalityObjEq A g)
    (translationCostructuredMapNaturalityIso_hom_app_eqToHom A g)

end General

section SmallUniverse

variable {C₀ : Type u} [Category.{u} C₀] [HasZeroMorphisms C₀]
  [HasZeroObject C₀] [HasBinaryBiproducts C₀]

/-- First-coordinate translation gives a natural transformation from the
right-comma nerve diagram to its precomposition by base translation. -/
noncomputable def translationRightCommaNerveDiagramNatTrans (A : C₀) :
    SSet.rightCommaNerveDiagram (translationProjection (C := C₀)) ⟶
      Translation.translateFunctor A ⋙
        SSet.rightCommaNerveDiagram (translationProjection (C := C₀)) where
  app B := nerveMap (translationCostructuredMap A B)
  naturality {B D} g := by
    change
      nerveMap (CostructuredArrow.map g) ≫
          nerveMap (translationCostructuredMap A D) =
        nerveMap (translationCostructuredMap A B) ≫
          nerveMap (CostructuredArrow.map
            ((Translation.translateFunctor A).map g))
    rw [nerveMap_comp, nerveMap_comp,
      translationCostructuredMap_naturality]

@[simp]
theorem translationRightCommaNerveDiagramNatTrans_app
    (A : C₀) (B : Translation C₀) :
    (translationRightCommaNerveDiagramNatTrans A).app B =
      nerveMap (translationCostructuredMap A B) :=
  rfl

end SmallUniverse

end SInverseS
end CategoryTheory

end
