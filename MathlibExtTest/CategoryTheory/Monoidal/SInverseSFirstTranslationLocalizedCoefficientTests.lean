/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.CategoryTheory.Monoidal.SInverseSFirstTranslationLocalizedCoefficient

/-! # Tests for the directly localized first-translation comparison -/

@[expose] public section

noncomputable section

open CategoryTheory Limits ZeroObject

namespace MathlibExtTest.SInverseSFirstTranslationLocalizedCoefficient

open CategoryTheory.SInverseS

variable (C : Type) [Category.{0} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]

#check coreTranslationHomologyLocalizationMap
#check coreTranslationCoefficientMap_comp_localizationMap
#check
  translationCostructured_homologyMap_comp_coreCoefficientComparison_comp_localizationMap

example (R : AddCommGrpCat.{0}) (q : ℕ) (x : Skeleton C) :
    (forget₂ (ModuleCat (coreTranslationRing C)) AddCommGrpCat).map
          (coreTranslationCoefficientMap C R q x) ≫
        coreTranslationHomologyLocalizationMap C R q =
      coreTranslationHomologyLocalizationMap C R q ≫
        (forget₂
          (ModuleCat (Localization (coreTranslationDenominators C)))
          AddCommGrpCat).map
          (localizedCoreTranslationEquiv C R q x).toModuleIso.hom :=
  coreTranslationCoefficientMap_comp_localizationMap C R q x

example (R : AddCommGrpCat.{0}) (A : C) (B : Translation C) (q : ℕ) :
    SSet.homologyMap
          (nerveMap (translationCostructuredMap A B)) R q ≫
        (costructuredCoreTranslationCoefficientNatIso C R q).hom.app
          ((Translation.translateFunctor A).obj B) ≫
        coreTranslationHomologyLocalizationMap C R q =
      (costructuredCoreTranslationCoefficientNatIso C R q).hom.app B ≫
        coreTranslationHomologyLocalizationMap C R q :=
  translationCostructured_homologyMap_comp_coreCoefficientComparison_comp_localizationMap
    C R A B q

-- Boundary `A = 0`: cancellation still occurs only after localization.
example (R : AddCommGrpCat.{0}) (B : Translation C) (q : ℕ) :
    SSet.homologyMap
          (nerveMap (translationCostructuredMap (0 : C) B)) R q ≫
        (costructuredCoreTranslationCoefficientNatIso C R q).hom.app
          ((Translation.translateFunctor (0 : C)).obj B) ≫
        coreTranslationHomologyLocalizationMap C R q =
      (costructuredCoreTranslationCoefficientNatIso C R q).hom.app B ≫
        coreTranslationHomologyLocalizationMap C R q :=
  translationCostructured_homologyMap_comp_coreCoefficientComparison_comp_localizationMap
    C R (0 : C) B q

-- Boundary `B = 0`: the proof still localizes the monomial `[A]`.
example (R : AddCommGrpCat.{0}) (A : C) (q : ℕ) :
    SSet.homologyMap
          (nerveMap (translationCostructuredMap A
            (⟨(0 : C)⟩ : Translation C))) R q ≫
        (costructuredCoreTranslationCoefficientNatIso C R q).hom.app
          ((Translation.translateFunctor A).obj
            (⟨(0 : C)⟩ : Translation C)) ≫
        coreTranslationHomologyLocalizationMap C R q =
      (costructuredCoreTranslationCoefficientNatIso C R q).hom.app
          (⟨(0 : C)⟩ : Translation C) ≫
        coreTranslationHomologyLocalizationMap C R q :=
  translationCostructured_homologyMap_comp_coreCoefficientComparison_comp_localizationMap
    C R A _ q

-- Boundary `q = 0`: the same localized bridge applies in degree zero.
example (R : AddCommGrpCat.{0}) (A : C) (B : Translation C) :
    SSet.homologyMap
          (nerveMap (translationCostructuredMap A B)) R 0 ≫
        (costructuredCoreTranslationCoefficientNatIso C R 0).hom.app
          ((Translation.translateFunctor A).obj B) ≫
        coreTranslationHomologyLocalizationMap C R 0 =
      (costructuredCoreTranslationCoefficientNatIso C R 0).hom.app B ≫
        coreTranslationHomologyLocalizationMap C R 0 :=
  translationCostructured_homologyMap_comp_coreCoefficientComparison_comp_localizationMap
    C R A B 0

#print axioms coreTranslationHomologyLocalizationMap
#print axioms coreTranslationCoefficientMap_comp_localizationMap
#print axioms
  translationCostructured_homologyMap_comp_coreCoefficientComparison_comp_localizationMap

end MathlibExtTest.SInverseSFirstTranslationLocalizedCoefficient

end
