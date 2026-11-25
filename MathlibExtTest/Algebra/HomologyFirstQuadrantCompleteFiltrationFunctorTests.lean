/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.FirstQuadrantCompleteFiltrationFunctor

/-! # Tests for the complete horizontal-filtration functor -/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe v u

namespace HomologicalComplex₂.FirstQuadrantCompleteFiltrationFunctorTests

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasFiniteCoproducts C]
variable {K L : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ)}

#check horizontalCompleteTotalFilteredObjectFunctor
#check horizontalCompleteTotalFilteredObjectFunctor_obj
#check horizontalCompleteTotalFilteredObjectFunctor_map_hom
#check horizontalCompleteTotalFilteredObjectFunctor_map_natTrans_app

example :
    HomologicalComplex₂ C (ComplexShape.down ℕ)
        (ComplexShape.down ℕ) ⥤
      CategoryTheory.FilteredObject (ChainComplex C ℕ) EInt :=
  horizontalCompleteTotalFilteredObjectFunctor

example (f : K ⟶ L) :
    (horizontalCompleteTotalFilteredObjectFunctor.map f).hom =
      total.map f (ComplexShape.down ℕ) :=
  horizontalCompleteTotalFilteredObjectFunctor_map_hom f

example (f : K ⟶ L) (i : EInt) :
    (horizontalCompleteTotalFilteredObjectFunctor.map f).natTrans.app i =
      horizontalCompleteFilteredTotalComplexMapOfBicomplex f i :=
  horizontalCompleteTotalFilteredObjectFunctor_map_natTrans_app f i

#print axioms horizontalCompleteTotalFilteredObjectFunctor
#print axioms horizontalCompleteTotalFilteredObjectFunctor_obj
#print axioms horizontalCompleteTotalFilteredObjectFunctor_map_hom
#print axioms horizontalCompleteTotalFilteredObjectFunctor_map_natTrans_app

end HomologicalComplex₂.FirstQuadrantCompleteFiltrationFunctorTests

end
