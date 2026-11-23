/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.CategoryTheory.Monoidal.SInverseSFirstTranslationCoefficient

/-! # Tests for the right-multiplied first-translation equation -/

@[expose] public section

noncomputable section

open CategoryTheory Limits ZeroObject

namespace MathlibExtTest.SInverseSFirstTranslationCoefficient

open CategoryTheory.SInverseS

variable (C : Type) [Category.{0} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]

#check
  translationCostructured_homologyMap_comp_coreCoefficientComparison_comp_coreCoefficientMap

example (R : AddCommGrpCat.{0}) (A : C) (B : Translation C) (q : ℕ) :
    SSet.homologyMap
          (nerveMap (translationCostructuredMap A B)) R q ≫
        (costructuredCoreTranslationCoefficientNatIso C R q).hom.app
          ((Translation.translateFunctor A).obj B) ≫
        (forget₂ (ModuleCat (coreTranslationRing C)) AddCommGrpCat).map
          (coreTranslationCoefficientMap C R q (toSkeleton A)) =
      (costructuredCoreTranslationCoefficientNatIso C R q).hom.app B ≫
        (forget₂ (ModuleCat (coreTranslationRing C)) AddCommGrpCat).map
          (coreTranslationCoefficientMap C R q (toSkeleton A)) :=
  translationCostructured_homologyMap_comp_coreCoefficientComparison_comp_coreCoefficientMap
    C R A B q

-- Boundary `A = 0`: retain the unit monomial explicitly rather than treating
-- zero translation as definitionally the identity.
example (R : AddCommGrpCat.{0}) (B : Translation C) (q : ℕ) :
    SSet.homologyMap
          (nerveMap (translationCostructuredMap (0 : C) B)) R q ≫
        (costructuredCoreTranslationCoefficientNatIso C R q).hom.app
          ((Translation.translateFunctor (0 : C)).obj B) ≫
        (forget₂ (ModuleCat (coreTranslationRing C)) AddCommGrpCat).map
          (coreTranslationCoefficientMap C R q (toSkeleton (0 : C))) =
      (costructuredCoreTranslationCoefficientNatIso C R q).hom.app B ≫
        (forget₂ (ModuleCat (coreTranslationRing C)) AddCommGrpCat).map
          (coreTranslationCoefficientMap C R q (toSkeleton (0 : C))) :=
  translationCostructured_homologyMap_comp_coreCoefficientComparison_comp_coreCoefficientMap
    C R (0 : C) B q

-- Boundary `B = 0`: the right coefficient factor remains the monomial `[A]`.
example (R : AddCommGrpCat.{0}) (A : C) (q : ℕ) :
    SSet.homologyMap
          (nerveMap (translationCostructuredMap A
            (⟨(0 : C)⟩ : Translation C))) R q ≫
        (costructuredCoreTranslationCoefficientNatIso C R q).hom.app
          ((Translation.translateFunctor A).obj
            (⟨(0 : C)⟩ : Translation C)) ≫
        (forget₂ (ModuleCat (coreTranslationRing C)) AddCommGrpCat).map
          (coreTranslationCoefficientMap C R q (toSkeleton A)) =
      (costructuredCoreTranslationCoefficientNatIso C R q).hom.app
          (⟨(0 : C)⟩ : Translation C) ≫
        (forget₂ (ModuleCat (coreTranslationRing C)) AddCommGrpCat).map
          (coreTranslationCoefficientMap C R q (toSkeleton A)) :=
  translationCostructured_homologyMap_comp_coreCoefficientComparison_comp_coreCoefficientMap
    C R A _ q

-- Boundary `q = 0`: the same right-multiplied equation applies in degree zero.
example (R : AddCommGrpCat.{0}) (A : C) (B : Translation C) :
    SSet.homologyMap
          (nerveMap (translationCostructuredMap A B)) R 0 ≫
        (costructuredCoreTranslationCoefficientNatIso C R 0).hom.app
          ((Translation.translateFunctor A).obj B) ≫
        (forget₂ (ModuleCat (coreTranslationRing C)) AddCommGrpCat).map
          (coreTranslationCoefficientMap C R 0 (toSkeleton A)) =
      (costructuredCoreTranslationCoefficientNatIso C R 0).hom.app B ≫
        (forget₂ (ModuleCat (coreTranslationRing C)) AddCommGrpCat).map
          (coreTranslationCoefficientMap C R 0 (toSkeleton A)) :=
  translationCostructured_homologyMap_comp_coreCoefficientComparison_comp_coreCoefficientMap
    C R A B 0

#print axioms
  translationCostructured_homologyMap_comp_coreCoefficientComparison_comp_coreCoefficientMap

end MathlibExtTest.SInverseSFirstTranslationCoefficient

end
