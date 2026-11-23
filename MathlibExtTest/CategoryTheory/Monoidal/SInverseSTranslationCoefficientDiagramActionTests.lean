/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.CategoryTheory.Preadditive.SingleObj
public import Mathlib.Data.ZMod.Basic
public import
  MathlibExt.CategoryTheory.Monoidal.SInverseSTranslationCoefficientDiagramAction

/-! # Tests for the localized coefficient diagram action -/

@[expose] public section

noncomputable section

open CategoryTheory Limits ZeroObject

namespace MathlibExtTest.SInverseSTranslationCoefficientDiagramAction

open CategoryTheory.SInverseS

variable (C : Type) [Category.{0} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]

#check translationCostructuredHomologyNatTrans
#check translationCostructuredHomologyNatTrans_app
#check conjugatedFirstTranslationCoefficientAddCommGrpNatTrans
#check conjugatedFirstTranslationCoefficientAddCommGrpNatTrans_app
#check conjugatedFirstTranslationCoefficientModuleNatTrans
#check conjugatedFirstTranslationCoefficientModuleNatTrans_app
#check localizedConjugatedFirstTranslationCoefficientNatTrans
#check localizedConjugatedFirstTranslationCoefficientNatTrans_app
#check localizedConjugatedFirstTranslationCoefficientNatTrans_app_eq_id
#check localizedConjugatedFirstTranslationCoefficientNatTrans_eq

example (R : AddCommGrpCat.{0}) (q : ℕ) (A : C) (B : Translation C) :
    (translationCostructuredHomologyNatTrans C R q A).app B =
      SSet.homologyMap
        (nerveMap (translationCostructuredMap A B)) R q :=
  translationCostructuredHomologyNatTrans_app C R q A B

example (R : AddCommGrpCat.{0}) (q : ℕ) (A : C) (B : Translation C) :
    (conjugatedFirstTranslationCoefficientAddCommGrpNatTrans
      C R q A).app B =
        conjugatedFirstTranslationCoefficientMap C R q A B :=
  conjugatedFirstTranslationCoefficientAddCommGrpNatTrans_app
    C R q A B

example (R : AddCommGrpCat.{0}) (q : ℕ) (A : C) (B : Translation C) :
    (conjugatedFirstTranslationCoefficientModuleNatTrans
      C R q A).app B =
        conjugatedFirstTranslationCoefficientModuleMap C R q A B :=
  rfl

example (R : AddCommGrpCat.{0}) (q : ℕ) (A : C) (B : Translation C) :
    (localizedConjugatedFirstTranslationCoefficientNatTrans
      C R q A).app B =
        localizedConjugatedFirstTranslationCoefficientModuleMap
          C R q A B :=
  localizedConjugatedFirstTranslationCoefficientNatTrans_app
    C R q A B

example (R : AddCommGrpCat.{0}) (q : ℕ) (A : C) :
    localizedConjugatedFirstTranslationCoefficientNatTrans C R q A =
      (localizedCoreTranslationCoefficientTranslateNatIso
        C R q A).hom :=
  localizedConjugatedFirstTranslationCoefficientNatTrans_eq C R q A

example (R : AddCommGrpCat.{0}) (q : ℕ) (A : C)
    {B D : Translation C} (g : B ⟶ D) :
    (coreTranslationCoefficientFunctor C R q).map g ≫
        (conjugatedFirstTranslationCoefficientModuleNatTrans
          C R q A).app D =
      (conjugatedFirstTranslationCoefficientModuleNatTrans
          C R q A).app B ≫
        (Translation.translateFunctor A ⋙
          coreTranslationCoefficientFunctor C R q).map g :=
  (conjugatedFirstTranslationCoefficientModuleNatTrans
    C R q A).naturality g

example (R : AddCommGrpCat.{0}) (q : ℕ) (A : C)
    (B : Translation C) :
    (localizedConjugatedFirstTranslationCoefficientNatTrans
      C R q A).app B = 𝟙 _ := by
  exact localizedConjugatedFirstTranslationCoefficientNatTrans_app_eq_id
    C R q A B

example (R : AddCommGrpCat.{0}) (q : ℕ) (A : C)
    (B : Translation C) :
    (coreTranslationCoefficientFunctor C R q ⋙
          ModuleCat.localizedModuleFunctor
            (coreTranslationDenominators C)).map (𝟙 B) ≫
        (localizedConjugatedFirstTranslationCoefficientNatTrans
          C R q A).app B =
        (localizedConjugatedFirstTranslationCoefficientNatTrans
          C R q A).app B ≫
        (Translation.translateFunctor A ⋙
          (coreTranslationCoefficientFunctor C R q ⋙
            ModuleCat.localizedModuleFunctor
              (coreTranslationDenominators C))).map (𝟙 B) :=
  (localizedConjugatedFirstTranslationCoefficientNatTrans
    C R q A).naturality (𝟙 B)

example (R : AddCommGrpCat.{0}) (q : ℕ) (A : C)
    {B D E : Translation C} (g : B ⟶ D) (h : D ⟶ E) :
    (coreTranslationCoefficientFunctor C R q ⋙
          ModuleCat.localizedModuleFunctor
            (coreTranslationDenominators C)).map (g ≫ h) ≫
        (localizedConjugatedFirstTranslationCoefficientNatTrans
          C R q A).app E =
        (localizedConjugatedFirstTranslationCoefficientNatTrans
          C R q A).app B ≫
        (Translation.translateFunctor A ⋙
          (coreTranslationCoefficientFunctor C R q ⋙
            ModuleCat.localizedModuleFunctor
              (coreTranslationDenominators C))).map (g ≫ h) :=
  (localizedConjugatedFirstTranslationCoefficientNatTrans
    C R q A).naturality (g ≫ h)

example (R : AddCommGrpCat.{0}) (q : ℕ) (B : Translation C) :
    (localizedConjugatedFirstTranslationCoefficientNatTrans
      C R q (0 : C)).app B = 𝟙 _ := by
  exact localizedConjugatedFirstTranslationCoefficientNatTrans_app_eq_id
    C R q (0 : C) B

example (R : AddCommGrpCat.{0}) (q : ℕ) (A : C) :
    (localizedConjugatedFirstTranslationCoefficientNatTrans
      C R q A).app (0 : Translation C) = 𝟙 _ := by
  exact localizedConjugatedFirstTranslationCoefficientNatTrans_app_eq_id
    C R q A (0 : Translation C)

example (R : AddCommGrpCat.{0}) (A : C) (B : Translation C) :
    (localizedConjugatedFirstTranslationCoefficientNatTrans
      C R 0 A).app B = 𝟙 _ := by
  exact localizedConjugatedFirstTranslationCoefficientNatTrans_app_eq_id
    C R 0 A B

private abbrev ZeroCategory := SingleObj (ZMod 1)

private instance (X Y : ZeroCategory) : Subsingleton (X ⟶ Y) :=
  inferInstanceAs (Subsingleton (ZMod 1))

private instance : HasZeroObject ZeroCategory where
  zero :=
    ⟨SingleObj.star (ZMod 1),
      (IsZero.iff_id_eq_zero _).2 (Subsingleton.elim _ _)⟩

private instance : HasBinaryBiproducts ZeroCategory where
  has_binary_biproduct X Y := by
    apply hasBinaryBiproduct_of_total
      { pt := SingleObj.star (ZMod 1)
        fst := 0
        snd := 0
        inl := 0
        inr := 0
        inl_fst := Subsingleton.elim _ _
        inl_snd := Subsingleton.elim _ _
        inr_fst := Subsingleton.elim _ _
        inr_snd := Subsingleton.elim _ _ }
    exact Subsingleton.elim _ _

example (R : AddCommGrpCat.{0}) (q : ℕ)
    (A : ZeroCategory) (B : Translation ZeroCategory) :
    (localizedConjugatedFirstTranslationCoefficientNatTrans
      ZeroCategory R q A).app B = 𝟙 _ := by
  exact localizedConjugatedFirstTranslationCoefficientNatTrans_app_eq_id
    ZeroCategory R q A B

#print axioms translationCostructuredHomologyNatTrans
#print axioms translationCostructuredHomologyNatTrans_app
#print axioms conjugatedFirstTranslationCoefficientAddCommGrpNatTrans
#print axioms conjugatedFirstTranslationCoefficientAddCommGrpNatTrans_app
#print axioms conjugatedFirstTranslationCoefficientModuleNatTrans
#print axioms conjugatedFirstTranslationCoefficientModuleNatTrans_app
#print axioms localizedConjugatedFirstTranslationCoefficientNatTrans
#print axioms localizedConjugatedFirstTranslationCoefficientNatTrans_app
#print axioms
  localizedConjugatedFirstTranslationCoefficientNatTrans_app_eq_id
#print axioms localizedConjugatedFirstTranslationCoefficientNatTrans_eq

end MathlibExtTest.SInverseSTranslationCoefficientDiagramAction

end
