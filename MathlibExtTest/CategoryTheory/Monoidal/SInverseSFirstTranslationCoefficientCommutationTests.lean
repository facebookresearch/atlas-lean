/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.CategoryTheory.Monoidal.SInverseSFirstTranslationCoefficientCommutation

/-! # Tests for first-translation coefficient monomial commutation -/

@[expose] public section

noncomputable section

open CategoryTheory Limits ZeroObject

namespace MathlibExtTest.SInverseSFirstTranslationCoefficientCommutation

open CategoryTheory.SInverseS

variable (C : Type) [Category.{0} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]

#check conjugatedFirstTranslationCoefficientMap
#check conjugatedFirstTranslationCoefficientMap_comm_monomial

example (R : AddCommGrpCat.{0}) (q : ℕ) (A : C) (B : Translation C) :
    conjugatedFirstTranslationCoefficientMap C R q A B =
      (costructuredCoreTranslationCoefficientNatIso C R q).inv.app B ≫
        SSet.homologyMap
          (nerveMap (translationCostructuredMap A B)) R q ≫
        (costructuredCoreTranslationCoefficientNatIso C R q).hom.app
          ((Translation.translateFunctor A).obj B) :=
  rfl

example (R : AddCommGrpCat.{0}) (q : ℕ) (A : C) (B : Translation C)
    (x : Skeleton C) :
    conjugatedFirstTranslationCoefficientMap C R q A B ≫
        (forget₂ (ModuleCat (coreTranslationRing C)) AddCommGrpCat).map
          (coreTranslationCoefficientMap C R q x) =
      (forget₂ (ModuleCat (coreTranslationRing C)) AddCommGrpCat).map
          (coreTranslationCoefficientMap C R q x) ≫
        conjugatedFirstTranslationCoefficientMap C R q A B :=
  conjugatedFirstTranslationCoefficientMap_comm_monomial C R q A B x

-- The zero skeleton class is covered without treating its monomial map as a
-- cancellable morphism.
example (R : AddCommGrpCat.{0}) (q : ℕ) (A : C) (B : Translation C) :
    conjugatedFirstTranslationCoefficientMap C R q A B ≫
        (forget₂ (ModuleCat (coreTranslationRing C)) AddCommGrpCat).map
          (coreTranslationCoefficientMap C R q (0 : Skeleton C)) =
      (forget₂ (ModuleCat (coreTranslationRing C)) AddCommGrpCat).map
          (coreTranslationCoefficientMap C R q (0 : Skeleton C)) ≫
        conjugatedFirstTranslationCoefficientMap C R q A B :=
  conjugatedFirstTranslationCoefficientMap_comm_monomial C R q A B 0

-- Zero first-coordinate translation needs no definitional identity claim.
example (R : AddCommGrpCat.{0}) (q : ℕ) (B : Translation C)
    (x : Skeleton C) :
    conjugatedFirstTranslationCoefficientMap C R q (0 : C) B ≫
        (forget₂ (ModuleCat (coreTranslationRing C)) AddCommGrpCat).map
          (coreTranslationCoefficientMap C R q x) =
      (forget₂ (ModuleCat (coreTranslationRing C)) AddCommGrpCat).map
          (coreTranslationCoefficientMap C R q x) ≫
        conjugatedFirstTranslationCoefficientMap C R q (0 : C) B :=
  conjugatedFirstTranslationCoefficientMap_comm_monomial C R q (0 : C) B x

-- The zero base retains every monomial action.
example (R : AddCommGrpCat.{0}) (q : ℕ) (A : C) (x : Skeleton C) :
    conjugatedFirstTranslationCoefficientMap C R q A
          (⟨(0 : C)⟩ : Translation C) ≫
        (forget₂ (ModuleCat (coreTranslationRing C)) AddCommGrpCat).map
          (coreTranslationCoefficientMap C R q x) =
      (forget₂ (ModuleCat (coreTranslationRing C)) AddCommGrpCat).map
          (coreTranslationCoefficientMap C R q x) ≫
        conjugatedFirstTranslationCoefficientMap C R q A
          (⟨(0 : C)⟩ : Translation C) :=
  conjugatedFirstTranslationCoefficientMap_comm_monomial C R q A _ x

-- Degree-zero homology uses the same commutation argument.
example (R : AddCommGrpCat.{0}) (A : C) (B : Translation C)
    (x : Skeleton C) :
    conjugatedFirstTranslationCoefficientMap C R 0 A B ≫
        (forget₂ (ModuleCat (coreTranslationRing C)) AddCommGrpCat).map
          (coreTranslationCoefficientMap C R 0 x) =
      (forget₂ (ModuleCat (coreTranslationRing C)) AddCommGrpCat).map
          (coreTranslationCoefficientMap C R 0 x) ≫
        conjugatedFirstTranslationCoefficientMap C R 0 A B :=
  conjugatedFirstTranslationCoefficientMap_comm_monomial C R 0 A B x

#print axioms conjugatedFirstTranslationCoefficientMap
#print axioms conjugatedFirstTranslationCoefficientMap_comm_monomial

end MathlibExtTest.SInverseSFirstTranslationCoefficientCommutation

end
