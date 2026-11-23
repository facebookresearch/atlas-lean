/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.SInverseSTranslationBKBicomplexMap

/-! # Tests for translated additive S⁻¹S BK maps -/

@[expose] public section

noncomputable section

open CategoryTheory Limits ZeroObject

namespace MathlibExtTest.SInverseSTranslationBKBicomplexMap

variable (C : Type) [Category.{0} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]

open CategoryTheory.SInverseS

#check translatedRightCommaNerveDiagram
#check translationBKBicomplexMap
#check translationBKTotalComplexMap
#check translationBKTotalComplexMap_eq_totalFunctor_map
#check translationBKTotalHomologyMap

example (R : AddCommGrpCat) (A : C) :
    translationBKTotalComplexMap C R A =
      (HomologicalComplex₂.totalFunctor AddCommGrpCat
        (ComplexShape.down ℕ) (ComplexShape.down ℕ)
        (ComplexShape.down ℕ)).map
          (translationBKBicomplexMap C R A) :=
  translationBKTotalComplexMap_eq_totalFunctor_map C R A

#print axioms translationBKBicomplexMap
#print axioms translationBKTotalComplexMap
#print axioms translationBKTotalHomologyMap

end MathlibExtTest.SInverseSTranslationBKBicomplexMap

end
