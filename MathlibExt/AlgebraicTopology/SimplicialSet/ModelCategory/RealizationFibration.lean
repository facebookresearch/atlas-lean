/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.MinimalFibration.Realization.SSetRealizationMinimalFibration
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Realization.SSetRealizationBoundaryRLPFibration
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.MinimalFibration.Factorization
public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatModelStructure

/-!
# Realization of simplicial fibrations

The realization of a simplicial fibration has the selected right lifting
property against realized horns in every universe. It is therefore a
fibration in the opt-in TopCat model structure in every universe.
-/

@[expose] public section

open CategoryTheory HomotopicalAlgebra MorphismProperty
open scoped SSet.modelCategoryQuillen TopCat.modelCategory
universe u

namespace SSet

/-- The realization of a simplicial fibration lifts against every realized
horn inclusion. -/
theorem toTop_map_mem_realizedHornRLP
    {E B : SSet.{u}} (p : E ⟶ B) [Fibration p] :
    TopCat.realizedHornInclusions.{u}.rlp (SSet.toTop.map p) := by
  obtain ⟨E', r, p', hfac, hp'min, hrI⟩ :=
    MinimalFibration.factorization p
  have hr : TopCat.realizedHornInclusions.{u}.rlp
      (SSet.toTop.map r) :=
    SSet.toTop_map_mem_realizedHornRLP_of_I_rlp hrI
  have hp' : TopCat.realizedHornInclusions.{u}.rlp
      (SSet.toTop.map p') :=
    SSet.toTop_map_mem_realizedHornRLP_of_minimal p' hp'min
  have hcomp : TopCat.realizedHornInclusions.{u}.rlp
      (SSet.toTop.map r ≫ SSet.toTop.map p') :=
    MorphismProperty.comp_mem _ _ _ hr hp'
  simpa only [← Functor.map_comp, hfac] using hcomp

/-- The scope-gated TopCat fibration structure on the realization of a
simplicial fibration. -/
instance instFibrationToTopMap
    {E B : SSet.{u}} (p : E ⟶ B) [Fibration p] :
    Fibration (SSet.toTop.map p) := by
  rw [HomotopicalAlgebra.fibration_iff]
  exact SSet.toTop_map_mem_realizedHornRLP p

end SSet
