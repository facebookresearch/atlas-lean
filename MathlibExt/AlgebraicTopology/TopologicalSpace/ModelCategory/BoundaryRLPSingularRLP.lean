/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations
public import Mathlib.AlgebraicTopology.SingularSet
public import Mathlib.CategoryTheory.LiftingProperties.Adjunction
public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatGenerators

/-!
# Boundary-RLP transport across the realization/singular adjunction

This file is part of the KQ3 layer. A map in `TopCat` with the right lifting
property against all realized boundary inclusions is sent by the singular
functor `TopCat.toSSet` to a map with the right lifting property against
`SSet.modelCategoryQuillen.I`. For a simplicial boundary generator, the
adjunction lemma `sSetTopAdj.hasLiftingProperty_iff` moves the lifting
problem to the realized generator, where
`TopCat.boundary_mem_realizedBoundaryInclusions` applies.

This proves only the formal KQ3 transport half isolated by `v0910`. It does
not place `SSet.modelCategoryQuillen.I.rlp` maps in `SSet.KanComplex.W`,
claims no weak-equivalence result, and adds no model structure.
-/

@[expose] public section

open CategoryTheory

universe u

namespace TopCat

/-- Morphism-level transport: the singular image of a boundary-RLP map
lifts against every simplicial boundary generator. -/
theorem boundaryRLP_toSSet_mem_I_rlp {X Y : TopCat.{u}} {f : X ⟶ Y}
    (hf : realizedBoundaryInclusions.rlp f) {A B : SSet.{u}} {i : A ⟶ B}
    (hi : SSet.modelCategoryQuillen.I i) :
    HasLiftingProperty i (toSSet.map f) := by
  obtain ⟨n⟩ := hi
  exact (sSetTopAdj.hasLiftingProperty_iff (SSet.boundary n).ι f).mp
    (hf _ (boundary_mem_realizedBoundaryInclusions n))

/-- Property-level transport: boundary-RLP maps land in the inverse image
of `SSet.modelCategoryQuillen.I.rlp` under `TopCat.toSSet`. -/
theorem boundaryRLP_le_inverseImage_I_rlp :
    realizedBoundaryInclusions.rlp ≤
      (SSet.modelCategoryQuillen.I.rlp).inverseImage toSSet := by
  intro X Y f hf A B i hi
  exact boundaryRLP_toSSet_mem_I_rlp hf hi

end TopCat
