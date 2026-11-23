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
  MathlibExt.CategoryTheory.Monoidal.SInverseSTranslationCoefficientTranslate

/-! # Tests for translation invariance of the core coefficient functor -/

@[expose] public section

noncomputable section

open CategoryTheory Limits ZeroObject

namespace MathlibExtTest.SInverseSTranslationCoefficientTranslate

open CategoryTheory.SInverseS

variable (C : Type) [Category.{0} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]

#check translationStabilizerClass_translateFunctor_map
#check coreTranslationCoefficientTranslateNatIso
#check coreTranslationCoefficientTranslateNatIso_hom_app
#check coreTranslationCoefficientTranslateNatIso_inv_app
#check localizedCoreTranslationCoefficientTranslateNatIso
#check localizedCoreTranslationCoefficientTranslateNatIso_hom_app
#check localizedCoreTranslationCoefficientTranslateNatIso_inv_app

example (A : C) {B D : Translation C} (g : B ⟶ D) :
    translationStabilizerClass C
        ((Translation.translateFunctor A).map g) =
      translationStabilizerClass C g :=
  translationStabilizerClass_translateFunctor_map C A g

example (A : C) (B : Translation C) :
    translationStabilizerClass C
        ((Translation.translateFunctor A).map (𝟙 B)) =
      translationStabilizerClass C (𝟙 B) :=
  translationStabilizerClass_translateFunctor_map C A (𝟙 B)

example (A : C) {B D E : Translation C} (g : B ⟶ D) (h : D ⟶ E) :
    translationStabilizerClass C
        ((Translation.translateFunctor A).map (g ≫ h)) =
      translationStabilizerClass C (g ≫ h) :=
  translationStabilizerClass_translateFunctor_map C A (g ≫ h)

example {B D : Translation C} (g : B ⟶ D) :
    translationStabilizerClass C
        ((Translation.translateFunctor (0 : C)).map g) =
      translationStabilizerClass C g :=
  translationStabilizerClass_translateFunctor_map C (0 : C) g

example (A : C) {D : Translation C} (g : (0 : Translation C) ⟶ D) :
    translationStabilizerClass C
        ((Translation.translateFunctor A).map g) =
      translationStabilizerClass C g :=
  translationStabilizerClass_translateFunctor_map C A g

example (R : AddCommGrpCat.{0}) (q : ℕ) (A : C)
    {B D : Translation C} (g : B ⟶ D) :
    (coreTranslationCoefficientFunctor C R q).map g ≫
        (coreTranslationCoefficientTranslateNatIso C R q A).hom.app D =
      (coreTranslationCoefficientTranslateNatIso C R q A).hom.app B ≫
        (Translation.translateFunctor A ⋙
          coreTranslationCoefficientFunctor C R q).map g :=
  (coreTranslationCoefficientTranslateNatIso C R q A).hom.naturality g

example (R : AddCommGrpCat.{0}) (q : ℕ) (A : C) (B : Translation C) :
    (localizedCoreTranslationCoefficientTranslateNatIso
      C R q A).hom.app B = 𝟙 _ := by
  exact localizedCoreTranslationCoefficientTranslateNatIso_hom_app
    C R q A B

example (R : AddCommGrpCat.{0}) (A : C) (B : Translation C) :
    (localizedCoreTranslationCoefficientTranslateNatIso
      C R 0 A).inv.app B = 𝟙 _ := by
  exact localizedCoreTranslationCoefficientTranslateNatIso_inv_app
    C R 0 A B

example (R : AddCommGrpCat.{0}) (q : ℕ) (A : C) :
    (localizedCoreTranslationCoefficientTranslateNatIso
      C R q A).hom.app (0 : Translation C) = 𝟙 _ := by
  exact localizedCoreTranslationCoefficientTranslateNatIso_hom_app
    C R q A (0 : Translation C)

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
    (localizedCoreTranslationCoefficientTranslateNatIso
      ZeroCategory R q A).hom.app B = 𝟙 _ := by
  simp

#print axioms translationStabilizerClass_translateFunctor_map
#print axioms coreTranslationCoefficientTranslateNatIso
#print axioms coreTranslationCoefficientTranslateNatIso_hom_app
#print axioms coreTranslationCoefficientTranslateNatIso_inv_app
#print axioms localizedCoreTranslationCoefficientTranslateNatIso
#print axioms localizedCoreTranslationCoefficientTranslateNatIso_hom_app
#print axioms localizedCoreTranslationCoefficientTranslateNatIso_inv_app

end MathlibExtTest.SInverseSTranslationCoefficientTranslate

end
