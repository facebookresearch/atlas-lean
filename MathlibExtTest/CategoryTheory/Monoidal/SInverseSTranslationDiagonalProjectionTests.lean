/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.SInverseSTranslationDiagonalProjection

/-! # Tests for diagonal translation over the additive S⁻¹S projection -/

@[expose] public section

noncomputable section

open CategoryTheory Limits ZeroObject

universe v u

namespace MathlibExtTest.SInverseSTranslationDiagonalProjection

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  [HasZeroObject C] [HasBinaryBiproducts C]

open CategoryTheory.SInverseS

#check translationProjection_map_translateSecondFunctor_map
#check translateSecondProjectionIso
#check translateSecondFunctor_comp_translationProjection
#check diagonalTranslationFunctor
#check diagonalTranslationProjectionIso
#check diagonalTranslationFunctor_comp_translationProjection
#check translationProjection_map_diagonalAddFirstSecondNatTrans_app

example (A : C) :
    diagonalTranslationFunctor A ⋙ translationProjection =
      translationProjection ⋙ Translation.translateFunctor A :=
  diagonalTranslationFunctor_comp_translationProjection A

#print axioms translateSecondProjectionIso
#print axioms diagonalTranslationProjectionIso
#print axioms diagonalTranslationFunctor_comp_translationProjection
#print axioms translationProjection_map_diagonalAddFirstSecondNatTrans_app

end MathlibExtTest.SInverseSTranslationDiagonalProjection

end
