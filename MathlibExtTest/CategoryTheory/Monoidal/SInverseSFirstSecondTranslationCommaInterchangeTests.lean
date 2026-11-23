/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.CategoryTheory.Monoidal.SInverseSFirstSecondTranslationCommaInterchange

/-! # Tests for arbitrary-parameter coordinate-translation interchange -/

@[expose] public section

noncomputable section

open CategoryTheory Limits ZeroObject

universe v u

namespace MathlibExtTest.SInverseSFirstSecondTranslationCommaInterchange

open CategoryTheory.SInverseS

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  [HasZeroObject C] [HasBinaryBiproducts C]

#check RawHom.translateFirst_translateSecond_of_parameters
#check Hom.translateFirst_translateSecond_of_parameters
#check translateFirstFunctor_map_translateSecondFunctor_map
#check firstSecondTranslationCostructuredInterchangeIso
#check firstSecondTranslationCostructuredInterchangeIso_hom_app_left
#check firstSecondTranslationCostructuredNerveHomotopy
#check firstSecondTranslationCostructured_homologyMap_comm

example (A X : C) {Y Z : Pair C} (f : RawHom Y Z) :
    (f.translateFirst A).translateSecond X =
      (f.translateSecond X).translateFirst A :=
  RawHom.translateFirst_translateSecond_of_parameters A X f

example (A X : C) {Y Z : Pair C} (f : Hom Y Z) :
    Hom.translateSecond X (Hom.translateFirst A f) =
      Hom.translateFirst A (Hom.translateSecond X f) :=
  Hom.translateFirst_translateSecond_of_parameters A X f

example (A X : C) {Y Z : Pair C} (f : Y ⟶ Z) :
    (translateSecondFunctor X).map
        ((translateFirstFunctor A).map f) =
      (translateFirstFunctor A).map
        ((translateSecondFunctor X).map f) :=
  translateFirstFunctor_map_translateSecondFunctor_map A X f

example (A X : C) (B : Translation C) :
    translationCostructuredMap A B ⋙
        secondTranslationCostructuredMap X
          ((Translation.translateFunctor A).obj B) ≅
      secondTranslationCostructuredMap X B ⋙
        translationCostructuredMap A B :=
  firstSecondTranslationCostructuredInterchangeIso A X B

example (A X : C) (B : Translation C)
    (Y : CostructuredArrow (translationProjection (C := C)) B) :
    ((firstSecondTranslationCostructuredInterchangeIso
      A X B).hom.app Y).left = 𝟙 _ :=
  firstSecondTranslationCostructuredInterchangeIso_hom_app_left A X B Y

example (A X : C) (B : Translation C) :
    SSet.Homotopy
      (nerveMap (translationCostructuredMap A B) ≫
        nerveMap (secondTranslationCostructuredMap X
          ((Translation.translateFunctor A).obj B)))
      (nerveMap (secondTranslationCostructuredMap X B) ≫
        nerveMap (translationCostructuredMap A B)) :=
  firstSecondTranslationCostructuredNerveHomotopy A X B

-- The same-parameter case recovers the previously used coordinate order.
example (A : C) {Y Z : Pair C} (f : RawHom Y Z) :
    (f.translateFirst A).translateSecond A =
      (f.translateSecond A).translateFirst A :=
  RawHom.translateFirst_translateSecond_of_parameters A A f

-- Neither zero parameter is treated as a definitionally identity functor.
example (X : C) {Y Z : Pair C} (f : Y ⟶ Z) :
    (translateSecondFunctor X).map
        ((translateFirstFunctor (0 : C)).map f) =
      (translateFirstFunctor (0 : C)).map
        ((translateSecondFunctor X).map f) :=
  translateFirstFunctor_map_translateSecondFunctor_map (0 : C) X f

example (A : C) {Y Z : Pair C} (f : Y ⟶ Z) :
    (translateSecondFunctor (0 : C)).map
        ((translateFirstFunctor A).map f) =
      (translateFirstFunctor A).map
        ((translateSecondFunctor (0 : C)).map f) :=
  translateFirstFunctor_map_translateSecondFunctor_map A (0 : C) f

-- Boundary at the chosen zero base object.
example (A X : C) :
    translationCostructuredMap A (⟨(0 : C)⟩ : Translation C) ⋙
        secondTranslationCostructuredMap X
          ((Translation.translateFunctor A).obj
            (⟨(0 : C)⟩ : Translation C)) ≅
      secondTranslationCostructuredMap X
          (⟨(0 : C)⟩ : Translation C) ⋙
        translationCostructuredMap A
          (⟨(0 : C)⟩ : Translation C) :=
  firstSecondTranslationCostructuredInterchangeIso A X _

section Homology

variable (C₀ : Type) [Category.{0} C₀] [Preadditive C₀]
  [HasZeroObject C₀] [HasBinaryBiproducts C₀]

example (R : AddCommGrpCat.{0}) (q : ℕ)
    (A X : C₀) (B : Translation C₀) :
    SSet.homologyMap
          (nerveMap (translationCostructuredMap A B)) R q ≫
        SSet.homologyMap
          (nerveMap (secondTranslationCostructuredMap X
            ((Translation.translateFunctor A).obj B))) R q =
      SSet.homologyMap
          (nerveMap (secondTranslationCostructuredMap X B)) R q ≫
        SSet.homologyMap
          (nerveMap (translationCostructuredMap A B)) R q :=
  firstSecondTranslationCostructured_homologyMap_comm C₀ R q A X B

-- Degree-zero homology uses the identical interchange square.
example (R : AddCommGrpCat.{0})
    (A X : C₀) (B : Translation C₀) :
    SSet.homologyMap
          (nerveMap (translationCostructuredMap A B)) R 0 ≫
        SSet.homologyMap
          (nerveMap (secondTranslationCostructuredMap X
            ((Translation.translateFunctor A).obj B))) R 0 =
      SSet.homologyMap
          (nerveMap (secondTranslationCostructuredMap X B)) R 0 ≫
        SSet.homologyMap
          (nerveMap (translationCostructuredMap A B)) R 0 :=
  firstSecondTranslationCostructured_homologyMap_comm C₀ R 0 A X B

end Homology

#print axioms RawHom.translateFirst_translateSecond_of_parameters
#print axioms Hom.translateFirst_translateSecond_of_parameters
#print axioms firstSecondTranslationCostructuredInterchangeIso
#print axioms firstSecondTranslationCostructuredNerveHomotopy
#print axioms firstSecondTranslationCostructured_homologyMap_comm

end MathlibExtTest.SInverseSFirstSecondTranslationCommaInterchange

end
