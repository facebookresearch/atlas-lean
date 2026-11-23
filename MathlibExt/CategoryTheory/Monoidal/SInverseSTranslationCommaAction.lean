/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import MathlibExt.CategoryTheory.Monoidal.SInverseSTranslationBaseAction

/-!
# Translation on right-comma categories of additive S⁻¹S

The identity-component square relating first-coordinate translation to base
translation induces, through `CostructuredArrow.map₂`, a functor between the
corresponding right-comma categories.  These functors are natural in the
chosen base object.  This is the comma-category layer of translation
equivariance and reuses Mathlib's existing comma construction.

No comparison with the unshifted comma diagram is claimed here: that
comparison must pass through cocartesian diagonal pushforward and the
second-coordinate inverse.  This file also constructs no nerve-chain,
spectral-sequence, localization, realization, or CGWH map.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits ZeroObject

universe v u

namespace CategoryTheory
namespace SInverseS

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  [HasZeroObject C] [HasBinaryBiproducts C]

/-- First-coordinate translation induces a functor between the right-comma
categories over a base object and its left translation. -/
noncomputable def translationCostructuredMap (A : C) (B : Translation C) :
    CostructuredArrow (translationProjection (C := C)) B ⥤
      CostructuredArrow (translationProjection (C := C))
        ((Translation.translateFunctor A).obj B) :=
  CostructuredArrow.map₂
    (translateFirstProjectionIso A).hom
    (𝟙 ((Translation.translateFunctor A).obj B))

@[simp]
theorem translationCostructuredMap_obj_left
    (A : C) (B : Translation C)
    (X : CostructuredArrow (translationProjection (C := C)) B) :
    ((translationCostructuredMap A B).obj X).left =
      (translateFirstFunctor A).obj X.left :=
  rfl

@[simp]
theorem translationCostructuredMap_obj_hom
    (A : C) (B : Translation C)
    (X : CostructuredArrow (translationProjection (C := C)) B) :
    ((translationCostructuredMap A B).obj X).hom =
      (translateFirstProjectionIso A).hom.app X.left ≫
        (Translation.translateFunctor A).map X.hom ≫
        𝟙 ((Translation.translateFunctor A).obj B) :=
  CostructuredArrow.map₂_obj_hom _ _ _

@[simp]
theorem translationCostructuredMap_map_left
    (A : C) (B : Translation C)
    {X Y : CostructuredArrow (translationProjection (C := C)) B}
    (f : X ⟶ Y) :
    ((translationCostructuredMap A B).map f).left =
      (translateFirstFunctor A).map f.left :=
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The translated right-comma functors commute, up to their canonical
identity-left-component isomorphism, with base change in the translation
category. -/
noncomputable def translationCostructuredMapNaturalityIso
    (A : C) {B D : Translation C} (g : B ⟶ D) :
    CostructuredArrow.map g ⋙ translationCostructuredMap A D ≅
      translationCostructuredMap A B ⋙
        CostructuredArrow.map ((Translation.translateFunctor A).map g) :=
  NatIso.ofComponents
    (fun X => CostructuredArrow.isoMk (Iso.refl _) (by
      simp [translationCostructuredMap]))
    (by
      intro X Y f
      apply CostructuredArrow.ext
      simp [Functor.comp_map, translationCostructuredMap])

@[simp]
theorem translationCostructuredMapNaturalityIso_hom_app_left
    (A : C) {B D : Translation C} (g : B ⟶ D)
    (X : CostructuredArrow (translationProjection (C := C)) B) :
    ((translationCostructuredMapNaturalityIso A g).hom.app X).left = 𝟙 _ :=
  by
    change (Iso.refl _).hom = 𝟙 _
    rfl

end SInverseS
end CategoryTheory

end
