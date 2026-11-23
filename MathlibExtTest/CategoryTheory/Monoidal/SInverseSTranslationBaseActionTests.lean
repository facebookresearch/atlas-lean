/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.SInverseSTranslationBaseAction

/-! # Tests for translation equivariance of the additive S⁻¹S projection -/

@[expose] public section

noncomputable section

open CategoryTheory Limits ZeroObject

universe v u

namespace MathlibExtTest.SInverseSTranslationBaseAction

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  [HasZeroObject C] [HasBinaryBiproducts C]

open CategoryTheory.SInverseS

#check Translation.translateObj
#check Translation.RawHom.translate
#check Translation.Hom.translate
#check Translation.translateFunctor
#check Translation.translateFunctor_obj
#check Translation.translateFunctor_map_mk
#check Translation.diagonalAddHom
#check Translation.diagonalAddNatTrans
#check Translation.diagonalAddNatTrans_app
#check translateFirstProjectionIso
#check translateFirstProjectionIso_hom_app
#check translateFirstFunctor_comp_translationProjection

example (A : C) :
    translateFirstFunctor A ⋙ translationProjection =
      translationProjection ⋙ Translation.translateFunctor A :=
  translateFirstFunctor_comp_translationProjection A

#print axioms Translation.translateFunctor
#print axioms Translation.diagonalAddNatTrans
#print axioms translateFirstProjectionIso
#print axioms translateFirstFunctor_comp_translationProjection

end MathlibExtTest.SInverseSTranslationBaseAction

end
