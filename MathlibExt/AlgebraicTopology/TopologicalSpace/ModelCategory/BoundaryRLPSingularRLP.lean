/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations
public import Mathlib.AlgebraicTopology.SingularSet
public import Mathlib.CategoryTheory.LiftingProperties.Adjunction
public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatGenerators

/-!
# Boundary lifting under realization and the singular functor

Let `f : X → Y` be a map of topological spaces with the right lifting property
against all geometric realizations of simplicial boundary inclusions. The singular
map `Sing(f)` has the right lifting property against every simplicial boundary
inclusion. This follows by transporting the lifting square through the
realization–singular adjunction, in the same universe.
-/

@[expose] public section

open CategoryTheory

universe u

namespace TopCat

/--
If a topological map lifts against all realized boundary inclusions, its singular
image lifts against each simplicial boundary generator.
-/
theorem boundaryRLP_toSSet_mem_I_rlp {X Y : TopCat.{u}} {f : X ⟶ Y}
    (hf : realizedBoundaryInclusions.rlp f) {A B : SSet.{u}} {i : A ⟶ B}
    (hi : SSet.modelCategoryQuillen.I i) :
    HasLiftingProperty i (toSSet.map f) := by
  obtain ⟨n⟩ := hi
  exact (sSetTopAdj.hasLiftingProperty_iff (SSet.boundary n).ι f).mp
    (hf _ (boundary_mem_realizedBoundaryInclusions n))

/--
The class of maps lifting against realized boundaries is contained in the singular
inverse image of the simplicial boundary right lifting class.
-/
theorem boundaryRLP_le_inverseImage_I_rlp :
    realizedBoundaryInclusions.rlp ≤
      (SSet.modelCategoryQuillen.I.rlp).inverseImage toSSet := by
  intro X Y f hf A B i hi
  exact boundaryRLP_toSSet_mem_I_rlp hf hi

end TopCat
