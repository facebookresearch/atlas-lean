/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.SInverseSSecondTranslationComma

/-! # Tests for second translation on additive S⁻¹S right-comma categories -/

@[expose] public section

noncomputable section

open CategoryTheory Limits ZeroObject

universe v u

namespace MathlibExtTest.SInverseSSecondTranslationComma

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  [HasZeroObject C] [HasBinaryBiproducts C]

open CategoryTheory.SInverseS

#check secondTranslationProjectionNatTrans
#check secondTranslationProjectionNatTrans_app
#check secondTranslationCostructuredMap
#check secondTranslationCostructuredMap_obj_left
#check secondTranslationCostructuredMap_obj_hom
#check secondTranslationCostructuredMap_map_left
#check firstSecondTranslationCostructuredIso
#check firstSecondTranslationCostructuredIso_hom_app_left

example (A : C) (B : Translation C) :
    translationCostructuredMap A B ⋙
        secondTranslationCostructuredMap A
          ((Translation.translateFunctor A).obj B) ≅
      diagonalTranslationCostructuredMap A B :=
  firstSecondTranslationCostructuredIso A B

#print axioms secondTranslationCostructuredMap
#print axioms firstSecondTranslationCostructuredIso

end MathlibExtTest.SInverseSSecondTranslationComma

end
