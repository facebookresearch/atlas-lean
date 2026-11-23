/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.SInverseSTranslationCommaDiagram

/-! # Tests for the translated additive S⁻¹S right-comma nerve diagram -/

@[expose] public section

noncomputable section

open CategoryTheory Limits ZeroObject

universe v u

namespace MathlibExtTest.SInverseSTranslationCommaDiagram

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  [HasZeroObject C] [HasBinaryBiproducts C]

open CategoryTheory.SInverseS

#check translationCostructuredMapNaturalityObjEq
#check translationCostructuredMapNaturalityIso_hom_app_eqToHom
#check translationCostructuredMap_naturality
#check translationRightCommaNerveDiagramNatTrans
#check translationRightCommaNerveDiagramNatTrans_app

example {C₀ : Type} [Category.{0} C₀] [HasZeroMorphisms C₀]
    [HasZeroObject C₀] [HasBinaryBiproducts C₀] (A : C₀) :
    SSet.rightCommaNerveDiagram (translationProjection (C := C₀)) ⟶
      Translation.translateFunctor A ⋙
        SSet.rightCommaNerveDiagram (translationProjection (C := C₀)) :=
  translationRightCommaNerveDiagramNatTrans A

#print axioms translationCostructuredMap_naturality
#print axioms translationRightCommaNerveDiagramNatTrans

end MathlibExtTest.SInverseSTranslationCommaDiagram

end
