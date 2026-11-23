/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.CategoryTheory.Monoidal.SInverseSSecondTranslationCoefficient

/-! # Tests for the second-translation coefficient action -/

@[expose] public section

noncomputable section

open CategoryTheory Limits ZeroObject

namespace MathlibExtTest.SInverseSSecondTranslationCoefficient

open CategoryTheory.SInverseS

variable (C : Type) [Category.{0} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]

#check secondTranslationCostructured_homologyMap_comp_coreCoefficientComparison

example (R : AddCommGrpCat.{0}) (A : C) (B : Translation C) (q : ℕ) :
    SSet.homologyMap
          (nerveMap (secondTranslationCostructuredMap A B)) R q ≫
        (costructuredCoreTranslationCoefficientNatIso C R q).hom.app B =
      (costructuredCoreTranslationCoefficientNatIso C R q).hom.app B ≫
        (forget₂ (ModuleCat (coreTranslationRing C)) AddCommGrpCat).map
          (coreTranslationCoefficientMap C R q (toSkeleton A)) :=
  secondTranslationCostructured_homologyMap_comp_coreCoefficientComparison
    C R A B q

-- The first-then-second factorization uses second translation over the
-- translated base, not over the original base.
example (R : AddCommGrpCat.{0}) (A : C) (B : Translation C) (q : ℕ) :
    SSet.homologyMap
          (nerveMap (secondTranslationCostructuredMap A
            ((Translation.translateFunctor A).obj B))) R q ≫
        (costructuredCoreTranslationCoefficientNatIso C R q).hom.app
          ((Translation.translateFunctor A).obj B) =
      (costructuredCoreTranslationCoefficientNatIso C R q).hom.app
          ((Translation.translateFunctor A).obj B) ≫
        (forget₂ (ModuleCat (coreTranslationRing C)) AddCommGrpCat).map
          (coreTranslationCoefficientMap C R q (toSkeleton A)) :=
  secondTranslationCostructured_homologyMap_comp_coreCoefficientComparison
    C R A ((Translation.translateFunctor A).obj B) q

-- Boundary `A = 0`: the theorem applies without treating zero translation
-- as definitionally the identity.
example (R : AddCommGrpCat.{0}) (B : Translation C) (q : ℕ) :
    SSet.homologyMap
          (nerveMap (secondTranslationCostructuredMap (0 : C) B)) R q ≫
        (costructuredCoreTranslationCoefficientNatIso C R q).hom.app B =
      (costructuredCoreTranslationCoefficientNatIso C R q).hom.app B ≫
        (forget₂ (ModuleCat (coreTranslationRing C)) AddCommGrpCat).map
          (coreTranslationCoefficientMap C R q (toSkeleton (0 : C))) :=
  secondTranslationCostructured_homologyMap_comp_coreCoefficientComparison
    C R (0 : C) B q

-- Boundary `B = 0`: the coefficient action remains the monomial `[A]`.
example (R : AddCommGrpCat.{0}) (A : C) (q : ℕ) :
    SSet.homologyMap
          (nerveMap (secondTranslationCostructuredMap A
            (⟨(0 : C)⟩ : Translation C))) R q ≫
        (costructuredCoreTranslationCoefficientNatIso C R q).hom.app
          (⟨(0 : C)⟩ : Translation C) =
      (costructuredCoreTranslationCoefficientNatIso C R q).hom.app
          (⟨(0 : C)⟩ : Translation C) ≫
        (forget₂ (ModuleCat (coreTranslationRing C)) AddCommGrpCat).map
          (coreTranslationCoefficientMap C R q (toSkeleton A)) :=
  secondTranslationCostructured_homologyMap_comp_coreCoefficientComparison
    C R A _ q

-- Boundary `q = 0`: no separate degree-zero argument is required.
example (R : AddCommGrpCat.{0}) (A : C) (B : Translation C) :
    SSet.homologyMap
          (nerveMap (secondTranslationCostructuredMap A B)) R 0 ≫
        (costructuredCoreTranslationCoefficientNatIso C R 0).hom.app B =
      (costructuredCoreTranslationCoefficientNatIso C R 0).hom.app B ≫
        (forget₂ (ModuleCat (coreTranslationRing C)) AddCommGrpCat).map
          (coreTranslationCoefficientMap C R 0 (toSkeleton A)) :=
  secondTranslationCostructured_homologyMap_comp_coreCoefficientComparison
    C R A B 0

#print axioms
  secondTranslationCostructured_homologyMap_comp_coreCoefficientComparison

end MathlibExtTest.SInverseSSecondTranslationCoefficient

end
