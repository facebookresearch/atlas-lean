/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Homology.FirstQuadrantCompleteFiltrationNaturality

/-!
# The complete horizontal-filtration functor

First-quadrant bicomplexes map functorially to chain complexes equipped with
their complete `EInt`-indexed horizontal filtration.  The object and morphism
constructions are the existing complete filtered object and its stagewise map;
functoriality follows from the corresponding identities for total-complex
maps and extensionality of filtered-object morphisms.
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

/-- First-quadrant bicomplexes map functorially to completely filtered total
complexes indexed by the extended integers. -/
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
