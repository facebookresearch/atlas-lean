/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Data.ZMod.Basic
public import Mathlib.CategoryTheory.Preadditive.SingleObj
public import
  MathlibExt.CategoryTheory.Monoidal.SInverseSFirstTranslationCoefficientLinear

/-! # Tests for the linear lift of conjugated first translation -/

@[expose] public section

noncomputable section

open CategoryTheory Limits ZeroObject

namespace MathlibExtTest.SInverseSFirstTranslationCoefficientLinear

open CategoryTheory.SInverseS

variable (C : Type) [Category.{0} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]

#check conjugatedFirstTranslationCoefficientLinearMap
#check conjugatedFirstTranslationCoefficientLinearMap_apply
#check conjugatedFirstTranslationCoefficientModuleMap
#check conjugatedFirstTranslationCoefficientModuleMap_forget

example (R : AddCommGrpCat.{0}) (q : ℕ) (A : C) (B : Translation C)
    (z : coreTranslationHomologyModule C R q) :
    conjugatedFirstTranslationCoefficientLinearMap C R q A B z =
      conjugatedFirstTranslationCoefficientMap C R q A B z := by
  simp

example (R : AddCommGrpCat.{0}) (q : ℕ) (A : C) (B : Translation C)
    (r : coreTranslationRing C)
    (z : coreTranslationHomologyModule C R q) :
    conjugatedFirstTranslationCoefficientLinearMap C R q A B (r • z) =
      r • conjugatedFirstTranslationCoefficientLinearMap C R q A B z :=
  (conjugatedFirstTranslationCoefficientLinearMap C R q A B).map_smul r z

example (R : AddCommGrpCat.{0}) (q : ℕ) (A : C) (B : Translation C)
    (x : Skeleton C) (z : coreTranslationHomologyModule C R q) :
    conjugatedFirstTranslationCoefficientLinearMap C R q A B
        (MonoidAlgebra.of ℤ (Multiplicative (Skeleton C))
          (Multiplicative.ofAdd x) • z) =
      MonoidAlgebra.of ℤ (Multiplicative (Skeleton C))
          (Multiplicative.ofAdd x) •
        conjugatedFirstTranslationCoefficientLinearMap C R q A B z :=
  (conjugatedFirstTranslationCoefficientLinearMap C R q A B).map_smul _ z

example (R : AddCommGrpCat.{0}) (q : ℕ) (B : Translation C)
    (z : coreTranslationHomologyModule C R q) :
    conjugatedFirstTranslationCoefficientLinearMap C R q (0 : C) B z =
      conjugatedFirstTranslationCoefficientMap C R q (0 : C) B z := by
  simp

example (R : AddCommGrpCat.{0}) (q : ℕ) (A : C)
    (z : coreTranslationHomologyModule C R q) :
    conjugatedFirstTranslationCoefficientLinearMap C R q A
        (⟨(0 : C)⟩ : Translation C) z =
      conjugatedFirstTranslationCoefficientMap C R q A
        (⟨(0 : C)⟩ : Translation C) z := by
  simp

example (R : AddCommGrpCat.{0}) (A : C) (B : Translation C)
    (z : coreTranslationHomologyModule C R 0) :
    conjugatedFirstTranslationCoefficientLinearMap C R 0 A B z =
      conjugatedFirstTranslationCoefficientMap C R 0 A B z := by
  simp

example (R : AddCommGrpCat.{0}) (q : ℕ) (A : C) (B : Translation C) :
    (forget₂ (ModuleCat (coreTranslationRing C)) AddCommGrpCat).map
        (conjugatedFirstTranslationCoefficientModuleMap C R q A B) =
      conjugatedFirstTranslationCoefficientMap C R q A B := by
  exact conjugatedFirstTranslationCoefficientModuleMap_forget C R q A B

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

example (R : AddCommGrpCat.{0}) (q : ℕ) :
    coreTranslationHomologyModule
        ZeroCategory R q →ₗ[coreTranslationRing ZeroCategory]
      coreTranslationHomologyModule ZeroCategory R q :=
  conjugatedFirstTranslationCoefficientLinearMap
    ZeroCategory R q (0 : ZeroCategory)
      (⟨(0 : ZeroCategory)⟩ : Translation ZeroCategory)

#print axioms conjugatedFirstTranslationCoefficientLinearMap
#print axioms conjugatedFirstTranslationCoefficientLinearMap_apply
#print axioms conjugatedFirstTranslationCoefficientModuleMap
#print axioms conjugatedFirstTranslationCoefficientModuleMap_forget

end MathlibExtTest.SInverseSFirstTranslationCoefficientLinear

end
