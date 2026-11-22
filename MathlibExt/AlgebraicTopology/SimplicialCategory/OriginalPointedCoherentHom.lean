/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalCoherentPointedWeakPreservation
import MathlibExt.AlgebraicTopology.SimplicialSet.BoundaryOneMapNaturality

/-!
# The full original coherent endpoint Hom functor on pointed simplicial sets

The two original one-boundary faces retain the supplied source and
target maps. Every full Under arrow gives the same original realized
Hom map and its exact endpoint equations. All original identity and
composition maps are kept.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalPointed

/-- The actual category of simplicial sets with their full original endpoint boundary. -/
abbrev Category := Under (∂Δ[1] : SSet.{u})

/-- The same full original initial endpoint map. -/
def source (X : Category.{u}) : (Δ[0] : SSet.{u}) ⟶ X.right :=
  SSet.boundary.ι (1 : Fin 2) ≫ X.hom

/-- The same full original terminal endpoint map. -/
def target (X : Category.{u}) : (Δ[0] : SSet.{u}) ⟶ X.right :=
  SSet.boundary.ι (0 : Fin 2) ≫ X.hom

/-- Every actual pointed arrow retains the same original source endpoint. -/
theorem source_map {X Y : Category.{u}} (f : X ⟶ Y) : source X ≫ f.right = source Y := by
  exact (Category.assoc _ _ _).trans (congrArg (fun h => SSet.boundary.ι (1 : Fin 2) ≫ h) (Under.w f))

/-- Every actual pointed arrow retains the same original target endpoint. -/
theorem target_map {X Y : Category.{u}} (f : X ⟶ Y) : target X ≫ f.right = target Y := by
  exact (Category.assoc _ _ _).trans (congrArg (fun h => SSet.boundary.ι (0 : Fin 2) ≫ h) (Under.w f))

/-- The source vertex is the literal original source endpoint map. -/
def sourceVertex (X : Category.{u}) : X.right _⦋0⦌ := SSet.yonedaEquiv (source X)

/-- The target vertex is the literal original terminal endpoint map. -/
def targetVertex (X : Category.{u}) : X.right _⦋0⦌ := SSet.yonedaEquiv (target X)

/-- Every original source vertex reads back its same pointed image. -/
theorem sourceVertex_map {X Y : Category.{u}} (f : X ⟶ Y) :
    f.right.app (op ⦋0⦌) (sourceVertex X) = sourceVertex Y :=
  (SSet.yonedaEquiv_comp (source X) f.right).symm.trans (congrArg SSet.yonedaEquiv (source_map f))

/-- Every original target vertex reads back its same pointed image. -/
theorem targetVertex_map {X Y : Category.{u}} (f : X ⟶ Y) :
    f.right.app (op ⦋0⦌) (targetVertex X) = targetVertex Y :=
  (SSet.yonedaEquiv_comp (target X) f.right).symm.trans (congrArg SSet.yonedaEquiv (target_map f))

/-- The entire original coherent Hom at the two same original endpoint maps. -/
def homObject (X : Category.{u}) : SSet.{u} := hom X.right (sourceVertex X) (targetVertex X)

/-- Every full original pointed arrow retains its same whole raw coherent Hom map. -/
def homMap {X Y : Category.{u}} (f : X ⟶ Y) : homObject X ⟶ homObject Y :=
  pointedHomMap f.right (sourceVertex_map f) (targetVertex_map f)

/-- The same original endpoint Hom map is weak whenever the actual full original pointed source map is categorical
weak. -/
theorem homMap_weak {X Y : Category.{u}} (f : X ⟶ Y)
    (hf : SSet.categoricalEquivalences f.right) : SSet.realizationWeakEquivalences (homMap f) :=
  pointedHomMap_weak_of_categorical f.right hf (sourceVertex_map f) (targetVertex_map f)

end CategoryTheory.CoherentRealization.OriginalPointed
