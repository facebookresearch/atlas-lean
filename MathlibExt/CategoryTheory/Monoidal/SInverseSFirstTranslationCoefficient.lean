/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.CategoryTheory.Monoidal.SInverseSTranslationCommaHomologyFactorization
public import
  MathlibExt.CategoryTheory.Monoidal.SInverseSDiagonalBaseChangeCoefficient
public import
  MathlibExt.CategoryTheory.Monoidal.SInverseSSecondTranslationCoefficient

/-!
# First translation on right-comma homology coefficients

After comparison with the core translation coefficient module, the
first-coordinate translation map agrees with the identity only after both
sides are postcomposed with the coefficient monomial for the translated
object.  The monomial remains present: this file makes no cancellation,
localization, or invertibility claim about it.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits ZeroObject

universe u

namespace CategoryTheory
namespace SInverseS

variable (C : Type u) [Category.{u} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]

/-- First-coordinate translation followed by the translated-base comparison
and the coefficient monomial equals the original-base comparison followed by
the same monomial. -/
theorem
    translationCostructured_homologyMap_comp_coreCoefficientComparison_comp_coreCoefficientMap
    (R : AddCommGrpCat.{u}) (A : C) (B : Translation C) (q : ℕ) :
    SSet.homologyMap
          (nerveMap (translationCostructuredMap A B)) R q ≫
        (costructuredCoreTranslationCoefficientNatIso C R q).hom.app
          ((Translation.translateFunctor A).obj B) ≫
        (forget₂ (ModuleCat.{u} (coreTranslationRing C)) AddCommGrpCat.{u}).map
          (coreTranslationCoefficientMap C R q (toSkeleton A)) =
      (costructuredCoreTranslationCoefficientNatIso C R q).hom.app B ≫
        (forget₂ (ModuleCat.{u} (coreTranslationRing C)) AddCommGrpCat.{u}).map
          (coreTranslationCoefficientMap C R q (toSkeleton A)) := by
  have hSecond :=
    secondTranslationCostructured_homologyMap_comp_coreCoefficientComparison
      C R A ((Translation.translateFunctor A).obj B) q
  have hFactor :=
    baseChange_homologyMap_eq_first_comp_second C R A B q
  calc
    SSet.homologyMap
          (nerveMap (translationCostructuredMap A B)) R q ≫
        (costructuredCoreTranslationCoefficientNatIso C R q).hom.app
            ((Translation.translateFunctor A).obj B) ≫
          (forget₂ (ModuleCat.{u} (coreTranslationRing C)) AddCommGrpCat.{u}).map
            (coreTranslationCoefficientMap C R q (toSkeleton A)) =
      SSet.homologyMap
          (nerveMap (translationCostructuredMap A B)) R q ≫
        (SSet.homologyMap
            (nerveMap (secondTranslationCostructuredMap A
              ((Translation.translateFunctor A).obj B))) R q ≫
          (costructuredCoreTranslationCoefficientNatIso C R q).hom.app
            ((Translation.translateFunctor A).obj B)) := by
      rw [← hSecond]
    _ = (SSet.homologyMap
            (nerveMap (translationCostructuredMap A B)) R q ≫
          SSet.homologyMap
            (nerveMap (secondTranslationCostructuredMap A
              ((Translation.translateFunctor A).obj B))) R q) ≫
        (costructuredCoreTranslationCoefficientNatIso C R q).hom.app
          ((Translation.translateFunctor A).obj B) :=
      (Category.assoc _ _ _).symm
    _ = SSet.homologyMap
          (nerveMap (CostructuredArrow.map
            ((Translation.diagonalAddNatTrans A).app B))) R q ≫
        (costructuredCoreTranslationCoefficientNatIso C R q).hom.app
          ((Translation.translateFunctor A).obj B) := by
      rw [← hFactor]
    _ = (costructuredCoreTranslationCoefficientNatIso C R q).hom.app B ≫
        (forget₂ (ModuleCat.{u} (coreTranslationRing C)) AddCommGrpCat.{u}).map
          (coreTranslationCoefficientMap C R q (toSkeleton A)) :=
      diagonalAdd_homologyMap_comp_coreCoefficientComparison C R q A B

end SInverseS
end CategoryTheory

end
