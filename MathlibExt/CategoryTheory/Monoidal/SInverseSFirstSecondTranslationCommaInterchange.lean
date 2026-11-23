/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Category.Grp.Abelian
public import MathlibExt.CategoryTheory.CategoryHomology.Basic
public import
  MathlibExt.CategoryTheory.Monoidal.SInverseSSecondTranslationCommaNaturality

/-!
# Interchange of first- and second-coordinate comma translations

Translation in the first coordinate by `A` and translation in the second
coordinate by an independent object `X` commute at the raw-arrow and quotient
levels.  Their induced right-comma functors therefore commute up to a
canonical identity-left-component natural isomorphism.  This yields a safe
nerve homotopy and the corresponding equality on category homology.

This file makes no coefficient, module-linearity, or localization claim.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits ZeroObject

universe v u

namespace CategoryTheory
namespace SInverseS

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  [HasZeroObject C] [HasBinaryBiproducts C]

omit [HasZeroObject C] in
/-- First- and second-coordinate translation by independent parameters
commute definitionally on raw stabilized arrows. -/
theorem RawHom.translateFirst_translateSecond_of_parameters
    (A X : C) {Y Z : Pair C} (f : RawHom Y Z) :
    (f.translateFirst A).translateSecond X =
      (f.translateSecond X).translateFirst A :=
  rfl

omit [HasZeroObject C] in
/-- The arbitrary-parameter coordinate interchange descends to quotient
arrows. -/
theorem Hom.translateFirst_translateSecond_of_parameters
    (A X : C) {Y Z : Pair C} (f : Hom Y Z) :
    Hom.translateSecond X (Hom.translateFirst A f) =
      Hom.translateFirst A (Hom.translateSecond X f) := by
  induction f using Quotient.inductionOn
  rfl

/-- Functor-map form of arbitrary-parameter coordinate interchange. -/
theorem translateFirstFunctor_map_translateSecondFunctor_map
    (A X : C) {Y Z : Pair C} (f : Y ⟶ Z) :
    (translateSecondFunctor X).map
        ((translateFirstFunctor A).map f) =
      (translateFirstFunctor A).map
        ((translateSecondFunctor X).map f) :=
  Hom.translateFirst_translateSecond_of_parameters A X f

/-- First-coordinate comma translation and independent fiberwise
second-coordinate translation commute up to a canonical isomorphism. -/
noncomputable def firstSecondTranslationCostructuredInterchangeIso
    (A X : C) (B : Translation C) :
    translationCostructuredMap A B ⋙
        secondTranslationCostructuredMap X
          ((Translation.translateFunctor A).obj B) ≅
      secondTranslationCostructuredMap X B ⋙
        translationCostructuredMap A B :=
  NatIso.ofComponents
    (fun _ => CostructuredArrow.isoMk (Iso.refl _) (by
      simp [translationCostructuredMap,
        secondTranslationCostructuredMap,
        secondTranslationProjectionNatTrans]))
    (by
      intro Y Z f
      apply CostructuredArrow.ext
      simp [Functor.comp_map, translationCostructuredMap,
        secondTranslationCostructuredMap,
        secondTranslationProjectionNatTrans,
        translateFirstFunctor_map_translateSecondFunctor_map])

@[simp]
theorem firstSecondTranslationCostructuredInterchangeIso_hom_app_left
    (A X : C) (B : Translation C)
    (Y : CostructuredArrow (translationProjection (C := C)) B) :
    ((firstSecondTranslationCostructuredInterchangeIso
      A X B).hom.app Y).left = 𝟙 _ := by
  change (Iso.refl _).hom = 𝟙 _
  rfl

/-- The two orders of independent coordinate translation on a right-comma
category induce simplicially homotopic nerve maps. -/
noncomputable def firstSecondTranslationCostructuredNerveHomotopy
    (A X : C) (B : Translation C) :
    SSet.Homotopy
      (nerveMap (translationCostructuredMap A B) ≫
        nerveMap (secondTranslationCostructuredMap X
          ((Translation.translateFunctor A).obj B)))
      (nerveMap (secondTranslationCostructuredMap X B) ≫
        nerveMap (translationCostructuredMap A B)) := by
  simpa only [nerveMap_comp] using
    NatTrans.nerveHomotopy
      (firstSecondTranslationCostructuredInterchangeIso A X B).hom

section Homology

variable (C : Type u) [Category.{u} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]

/-- On right-comma homology, first-coordinate translation commutes with
fiberwise second-coordinate translation by an independent object. -/
theorem firstSecondTranslationCostructured_homologyMap_comm
    (R : AddCommGrpCat.{u}) (q : ℕ)
    (A X : C) (B : Translation C) :
    SSet.homologyMap
          (nerveMap (translationCostructuredMap A B)) R q ≫
        SSet.homologyMap
          (nerveMap (secondTranslationCostructuredMap X
            ((Translation.translateFunctor A).obj B))) R q =
      SSet.homologyMap
          (nerveMap (secondTranslationCostructuredMap X B)) R q ≫
        SSet.homologyMap
          (nerveMap (translationCostructuredMap A B)) R q := by
  rw [← SSet.homologyMap_comp, ← SSet.homologyMap_comp]
  exact (firstSecondTranslationCostructuredNerveHomotopy
    A X B).congr_homologyMap R q

end Homology

end SInverseS
end CategoryTheory

end
