/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.CategoryTheory.Monoidal.SInverseSDiagonalBaseChangeCoefficient

/-! # Tests for canonical base change on right-comma coefficients -/

@[expose] public section

noncomputable section

open CategoryTheory Limits ZeroObject

namespace MathlibExtTest.SInverseSDiagonalBaseChangeCoefficient

open CategoryTheory.SInverseS

variable (C : Type) [Category.{0} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]

#check diagonalAdd_homologyMap_comp_coreCoefficientComparison

example (R : AddCommGrpCat.{0}) (q : ℕ) (A : C) (B : Translation C) :
    SSet.homologyMap
          (nerveMap (CostructuredArrow.map
            ((Translation.diagonalAddNatTrans A).app B))) R q ≫
        (costructuredCoreTranslationCoefficientNatIso C R q).hom.app
          ((Translation.translateFunctor A).obj B) =
      (costructuredCoreTranslationCoefficientNatIso C R q).hom.app B ≫
        (forget₂ (ModuleCat (coreTranslationRing C)) AddCommGrpCat).map
          (coreTranslationCoefficientMap C R q (toSkeleton A)) :=
  diagonalAdd_homologyMap_comp_coreCoefficientComparison C R q A B

-- Boundary check: zero translation, zero base, and degree zero require no
-- separate argument or cancellation.
example (R : AddCommGrpCat.{0}) :
    SSet.homologyMap
          (nerveMap (CostructuredArrow.map
            ((Translation.diagonalAddNatTrans (0 : C)).app
              (⟨(0 : C)⟩ : Translation C)))) R 0 ≫
        (costructuredCoreTranslationCoefficientNatIso C R 0).hom.app
          ((Translation.translateFunctor (0 : C)).obj
            (⟨(0 : C)⟩ : Translation C)) =
      (costructuredCoreTranslationCoefficientNatIso C R 0).hom.app
          (⟨(0 : C)⟩ : Translation C) ≫
        (forget₂ (ModuleCat (coreTranslationRing C)) AddCommGrpCat).map
          (coreTranslationCoefficientMap C R 0 (toSkeleton (0 : C))) :=
  diagonalAdd_homologyMap_comp_coreCoefficientComparison C R 0 (0 : C) _

#print axioms diagonalAdd_homologyMap_comp_coreCoefficientComparison

end MathlibExtTest.SInverseSDiagonalBaseChangeCoefficient

end
