/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import
  MathlibExt.Algebra.Homology.FirstQuadrantHomologyFilteredObjectFunctor

/-! # Tests for the finite total-homology filtered-object functor -/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe v u

namespace HomologicalComplex₂.FirstQuadrantHomologyFilteredObjectFunctorTests

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K L : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ)}

#check horizontalFiniteTotalHomologyFilteredObjectFunctor
#check horizontalFiniteTotalHomologyFilteredObjectFunctor_obj_X
#check horizontalFiniteTotalHomologyFilteredObjectFunctor_obj_filtration
#check horizontalFiniteTotalHomologyFilteredObjectFunctor_map_hom
#check horizontalFiniteTotalHomologyFilteredObjectFunctor_map_natTrans_app

example (n : ℕ) :
    HomologicalComplex₂ C (ComplexShape.down ℕ)
        (ComplexShape.down ℕ) ⥤
      CategoryTheory.FilteredObject C ℕ :=
  horizontalFiniteTotalHomologyFilteredObjectFunctor n

example (n : ℕ) (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ)) :
    ((horizontalFiniteTotalHomologyFilteredObjectFunctor n).obj K).X =
      (K.total (ComplexShape.down ℕ)).homology n := by
  simp

example (n : ℕ) (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ)) :
    ((horizontalFiniteTotalHomologyFilteredObjectFunctor n).obj K).filtration =
      horizontalFiniteTotalHomologyFiltration K n := by
  simp

example (n : ℕ) (f : K ⟶ L) :
    ((horizontalFiniteTotalHomologyFilteredObjectFunctor n).map f).hom =
      HomologicalComplex.homologyMap
        (total.map f (ComplexShape.down ℕ)) n := by
  simp

example (n i : ℕ) (f : K ⟶ L) :
    ((horizontalFiniteTotalHomologyFilteredObjectFunctor n).map f).natTrans.app i =
      horizontalFiniteHomologyImageMapOfBicomplex f n i :=
  horizontalFiniteTotalHomologyFilteredObjectFunctor_map_natTrans_app n f i

example (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ)) :
    ((horizontalFiniteTotalHomologyFilteredObjectFunctor 0).obj K).filtration.obj 0 =
      (horizontalFiniteTotalHomologyFiltration K 0).obj 0 := by
  simp

example (n : ℕ) (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ)) :
    (horizontalFiniteTotalHomologyFilteredObjectFunctor n).map (𝟙 K) =
      𝟙 ((horizontalFiniteTotalHomologyFilteredObjectFunctor n).obj K) :=
  (horizontalFiniteTotalHomologyFilteredObjectFunctor n).map_id K

example (n i : ℕ) (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ)) :
    ((horizontalFiniteTotalHomologyFilteredObjectFunctor n).map
      (𝟙 K)).natTrans.app i =
        𝟙 ((horizontalFiniteTotalHomologyFiltration K n).obj i) := by
  simp

#print axioms horizontalFiniteTotalHomologyFilteredObjectFunctor
#print axioms horizontalFiniteTotalHomologyFilteredObjectFunctor_map_natTrans_app

end HomologicalComplex₂.FirstQuadrantHomologyFilteredObjectFunctorTests

end
