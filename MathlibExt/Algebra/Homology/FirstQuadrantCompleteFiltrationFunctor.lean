/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.FirstQuadrantCompleteFiltrationNaturality

/-!
# The functor of completely filtered first-quadrant total complexes

Let C be preadditive with a zero object and finite coproducts. A bicomplex K of shape (down
ℕ,down ℕ) is sent to its total chain complex with the complete horizontal filtration indexed by
ℤ∪{⊥,⊤}. Bottom and negative finite stages are zero, finite a≥0 stages are horizontal
truncations, and the top stage is Tot K.

A bicomplex morphism f:K→L is sent to the filtered-object morphism whose total map is Tot f and
whose component at each cut i is G_i(f):G_i(K)→G_i(L). Those components commute with stage
transitions and inclusions into the total complex. The assignments preserve identity maps and
composition, with arbitrary object and morphism universes.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasFiniteCoproducts C]
variable {K L : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ)}

/-- Let C be a preadditive category with a zero object and finite coproducts. This functor sends
bicomplexes of shape (down ℕ,down ℕ) to chain complexes equipped with an increasing filtration
indexed by ℤ∪{⊥,⊤}. Its value on K is Tot K with complete horizontal stages G_⊥=0, G_a=0 for
finite a<0, G_a the ath horizontal stage for a≥0, and G_⊤=Tot K. A morphism f is sent to Tot f
together with all stage maps G_i(f); identity and composition are preserved. -/
noncomputable def horizontalCompleteTotalFilteredObjectFunctor :
    HomologicalComplex₂ C (ComplexShape.down ℕ)
        (ComplexShape.down ℕ) ⥤
      CategoryTheory.FilteredObject (ChainComplex C ℕ) EInt where
  obj := horizontalCompleteTotalFilteredObject
  map := horizontalCompleteTotalFilteredObjectMap
  map_id K := by
    apply CategoryTheory.FilteredObject.hom_ext
    exact total.map_id K (ComplexShape.down ℕ)
  map_comp f g := by
    apply CategoryTheory.FilteredObject.hom_ext
    exact total.map_comp f g (ComplexShape.down ℕ)

@[simp]
theorem horizontalCompleteTotalFilteredObjectFunctor_obj
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) :
    horizontalCompleteTotalFilteredObjectFunctor.obj K =
      horizontalCompleteTotalFilteredObject K :=
  rfl

@[simp]
theorem horizontalCompleteTotalFilteredObjectFunctor_map_hom (f : K ⟶ L) :
    (horizontalCompleteTotalFilteredObjectFunctor.map f).hom =
      total.map f (ComplexShape.down ℕ) :=
  rfl

@[simp]
theorem horizontalCompleteTotalFilteredObjectFunctor_map_natTrans_app
    (f : K ⟶ L) (i : EInt) :
    (horizontalCompleteTotalFilteredObjectFunctor.map f).natTrans.app i =
      horizontalCompleteFilteredTotalComplexMapOfBicomplex f i :=
  rfl

end HomologicalComplex₂

end
