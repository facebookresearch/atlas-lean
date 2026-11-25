/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.FirstQuadrantFiltrationNaturality

/-! # Tests for naturality of the first-quadrant filtration -/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe v u

namespace HomologicalComplex₂.FirstQuadrantFiltrationNaturalityTests

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasFiniteCoproducts C]
variable {K L : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ)}

#check horizontalFilteredTotalMapOfBicomplex
#check horizontalFilteredTotalι_mapOfBicomplex
#check horizontalFilteredTotalMapOfBicomplex_toTotal
#check horizontalFilteredTotalComplexMapOfBicomplex
#check horizontalFilteredTotalComplexMapOfBicomplex_naturality
#check horizontalTotalFilteredObject
#check horizontalTotalFilteredObjectMap
#check horizontalTotalFilteredObjectFunctor

example (f : K ⟶ L) :
    horizontalTotalFilteredObject K ⟶
      horizontalTotalFilteredObject L :=
  horizontalTotalFilteredObjectMap f

example :
    HomologicalComplex₂ C (ComplexShape.down ℕ)
        (ComplexShape.down ℕ) ⥤
      CategoryTheory.FilteredObject (ChainComplex C ℕ) ℕ :=
  horizontalTotalFilteredObjectFunctor

#print axioms horizontalFilteredTotalComplexMapOfBicomplex
#print axioms horizontalFilteredTotalComplexMapOfBicomplex_naturality
#print axioms horizontalTotalFilteredObjectMap
#print axioms horizontalTotalFilteredObjectFunctor

end HomologicalComplex₂.FirstQuadrantFiltrationNaturalityTests

end
