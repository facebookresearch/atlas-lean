/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.SInverseSTranslationCommaHomologyFactorization

/-! # Tests for the translated right-comma homology factorization -/

@[expose] public section

noncomputable section

open CategoryTheory Limits ZeroObject

namespace MathlibExtTest.SInverseSTranslationCommaHomologyFactorization

variable (C : Type) [Category.{0} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]

open CategoryTheory.SInverseS

#check baseChange_homologyMap_eq_diagonalTranslation
#check firstSecond_homologyMap_eq_diagonalTranslation
#check baseChange_homologyMap_eq_first_comp_second

example (R : AddCommGrpCat) (A : C) (B : Translation C) (n : ℕ) :
    SSet.homologyMap
        (nerveMap (CostructuredArrow.map
          ((Translation.diagonalAddNatTrans A).app B))) R n =
      SSet.homologyMap
          (nerveMap (translationCostructuredMap A B)) R n ≫
        SSet.homologyMap
          (nerveMap (secondTranslationCostructuredMap A
            ((Translation.translateFunctor A).obj B))) R n :=
  baseChange_homologyMap_eq_first_comp_second C R A B n

#print axioms baseChange_homologyMap_eq_diagonalTranslation
#print axioms firstSecond_homologyMap_eq_diagonalTranslation
#print axioms baseChange_homologyMap_eq_first_comp_second

end MathlibExtTest.SInverseSTranslationCommaHomologyFactorization

end
