/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.SInverseSTranslationDiagonalComma

/-! # Tests for diagonal translation on additive S⁻¹S right-comma categories -/

@[expose] public section

noncomputable section

open CategoryTheory Limits ZeroObject

universe v u

namespace MathlibExtTest.SInverseSTranslationDiagonalComma

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  [HasZeroObject C] [HasBinaryBiproducts C]

open CategoryTheory.SInverseS

#check diagonalTranslationCostructuredMap
#check diagonalTranslationCostructuredMap_obj_left
#check diagonalTranslationCostructuredMap_obj_hom
#check diagonalTranslationCostructuredMap_map_left
#check baseChangeToDiagonalTranslationNatTrans
#check baseChangeToDiagonalTranslationNatTrans_app_left
#check baseChangeToDiagonalTranslationNerveHomotopy

example (A : C) (B : Translation C) :
    SSet.Homotopy
      (nerveMap
        (CostructuredArrow.map
          ((Translation.diagonalAddNatTrans A).app B)))
      (nerveMap (diagonalTranslationCostructuredMap A B)) :=
  baseChangeToDiagonalTranslationNerveHomotopy A B

#print axioms diagonalTranslationCostructuredMap
#print axioms baseChangeToDiagonalTranslationNatTrans
#print axioms baseChangeToDiagonalTranslationNerveHomotopy

end MathlibExtTest.SInverseSTranslationDiagonalComma

end
