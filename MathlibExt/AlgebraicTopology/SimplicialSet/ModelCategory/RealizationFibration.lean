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
# Geometric realization of Kan fibrations

For any simplicial Kan fibration p:E→B, the realized map |p| lifts against every realized horn
inclusion. In the selected TopCat model whose fibrations are this right-lifting class, |p| is
therefore a fibration.

The source and base simplicial sets are arbitrary, and the statement holds in every universe u.
-/

@[expose] public section

open CategoryTheory HomotopicalAlgebra MorphismProperty
open scoped SSet.modelCategoryQuillen TopCat.modelCategory
universe u

namespace SSet

/-- For any Kan fibration p:E→B of simplicial sets, |p|:|E|→|B| has the right lifting property
against every realized horn inclusion. -/
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

/-- For a simplicial Kan fibration p:E→B, its realization is a fibration in the TopCat model whose
fibration class is right lifting against realized horns. -/
instance instFibrationToTopMap
    {E B : SSet.{u}} (p : E ⟶ B) [Fibration p] :
    Fibration (SSet.toTop.map p) := by
  rw [HomotopicalAlgebra.fibration_iff]
  exact SSet.toTop_map_mem_realizedHornRLP p

end SSet
