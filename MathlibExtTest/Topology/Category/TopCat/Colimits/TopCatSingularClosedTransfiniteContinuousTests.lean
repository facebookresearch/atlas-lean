/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
MathlibExt.Topology.Category.TopCat.Colimits.TopCatSingularClosedTransfiniteContinuous

@[expose] public section

/-!
# Singular closed-transfinite continuity clients

Public clients for per-diagram singular well-order continuity at independent
diagram and ambient universes. The module also rejects global preservation
dictionaries and checks that later weak-equivalence APIs remain outside this
single-provider import boundary.
-/

set_option autoImplicit false

open CategoryTheory Limits

universe v u

namespace MathlibExtTest.AlgebraicTopology.ModelCategory
namespace TopCatSingularClosedTransfiniteContinuousTests

variable {J : Type v} [LinearOrder J] [OrderBot J]

/-- Per-diagram singular well-order continuity at an arbitrary universe. -/
theorem isWellOrderContinuous_comp_toSSet_of_closedT1_transfinite_client
    {F : J ⥤ TopCat.{u}} [F.IsWellOrderContinuous]
    (hF : ∀ ⦃i j : J⦄ (f : i ⟶ j),
      TopCat.closedT1Embeddings (F.map f)) :
    (F ⋙ TopCat.toSSet.{u}).IsWellOrderContinuous :=
  TopCat.isWellOrderContinuous_comp_toSSet_of_closedT1_transfinite hF

section UniverseOne

variable {J₁ : Type 1} [LinearOrder J₁] [OrderBot J₁]

/-- Concrete universe-one singular well-order continuity. -/
theorem isWellOrderContinuous_comp_toSSet_universeOne_client
    {F : J₁ ⥤ TopCat.{1}} [F.IsWellOrderContinuous]
    (hF : ∀ ⦃i j : J₁⦄ (f : i ⟶ j),
      TopCat.closedT1Embeddings (F.map f)) :
    (F ⋙ TopCat.toSSet.{1}).IsWellOrderContinuous :=
  TopCat.isWellOrderContinuous_comp_toSSet_of_closedT1_transfinite hF

end UniverseOne

/-- Original universe-zero singular well-order continuity. -/
theorem isWellOrderContinuous_comp_toSSet_universeZero_client
    {F : J ⥤ TopCat.{0}} [F.IsWellOrderContinuous]
    (hF : ∀ ⦃i j : J⦄ (f : i ⟶ j),
      TopCat.closedT1Embeddings (F.map f)) :
    (F ⋙ TopCat.toSSet.{0}).IsWellOrderContinuous :=
  TopCat.isWellOrderContinuous_comp_toSSet_of_closedT1_transfinite hF

/-- No global continuity or shape-wide colimit preservation is installed. -/
example : True := by
  fail_if_success
    let _ : PreservesWellOrderContinuousOfShape J TopCat.toSSet.{u} :=
      inferInstance
  fail_if_success
    let _ : PreservesColimitsOfShape J TopCat.toSSet.{u} := inferInstance
  trivial

section PullRequest4615Boundaries

/-- Unknown constant -/
#guard_msgs (error, substring := true) in
#check SSet.simplicialDiagonal_map_mem_realizationWeakEquivalences_of_inner_rows

/-- Unknown constant -/
#guard_msgs (error, substring := true) in
#check SSet.bkHocolimMap_mem_realizationWeakEquivalences

/-- Unknown identifier -/
#guard_msgs (error, substring := true) in
#check HomotopicalAlgebra.weakEquivalence_map_of_isPushouts_of_cofibrant

/-- Unknown constant -/
#guard_msgs (error, substring := true) in
#check SSet.realizationWeakEquivalences.of_isPushout_mono

/-- Unknown constant -/
#guard_msgs (error, substring := true) in
#check SSet.realizationWeakEquivalences.of_isColimit_nat_mono

end PullRequest4615Boundaries

#print axioms TopCat.isWellOrderContinuous_comp_toSSet_of_closedT1_transfinite
#print axioms isWellOrderContinuous_comp_toSSet_of_closedT1_transfinite_client
#print axioms isWellOrderContinuous_comp_toSSet_universeOne_client
#print axioms isWellOrderContinuous_comp_toSSet_universeZero_client

end TopCatSingularClosedTransfiniteContinuousTests
end MathlibExtTest.AlgebraicTopology.ModelCategory
