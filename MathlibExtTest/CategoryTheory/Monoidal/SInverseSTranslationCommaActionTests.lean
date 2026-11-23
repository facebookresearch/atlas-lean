/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.SInverseSTranslationCommaAction

/-! # Tests for translation on additive S⁻¹S right-comma categories -/

@[expose] public section

noncomputable section

open CategoryTheory Limits ZeroObject

universe v u

namespace MathlibExtTest.SInverseSTranslationCommaAction

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  [HasZeroObject C] [HasBinaryBiproducts C]

open CategoryTheory.SInverseS

#check translationCostructuredMap
#check translationCostructuredMap_obj_left
#check translationCostructuredMap_obj_hom
#check translationCostructuredMap_map_left
#check translationCostructuredMapNaturalityIso
#check translationCostructuredMapNaturalityIso_hom_app_left

example (A : C) {B D : Translation C} (g : B ⟶ D) :
    CostructuredArrow.map g ⋙ translationCostructuredMap A D ≅
      translationCostructuredMap A B ⋙
        CostructuredArrow.map ((Translation.translateFunctor A).map g) :=
  translationCostructuredMapNaturalityIso A g

#print axioms translationCostructuredMap
#print axioms translationCostructuredMapNaturalityIso

end MathlibExtTest.SInverseSTranslationCommaAction

end
