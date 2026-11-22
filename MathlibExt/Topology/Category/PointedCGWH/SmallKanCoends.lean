/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Enriched.Limits.WeightedCoend
public import MathlibExt.Topology.Category.PointedCGWH.Closed
public import MathlibExt.Topology.Category.CGWH.Colimits
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic

/-!
# Actual native small weighted coends

The native CGWH colimit provider and the generic undercategory construction
give pointed colimits of size (v,v). The actual size-shrink witness gives
size (0,0), hence precisely the full object/relation coproducts and parallel
coequalizer for any bare enriched source of type zero.
-/

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalClosed

namespace PointedCGWH.EnrichedKan
attribute [local instance] MonoidalClosed.enrichedCategorySelf

set_option maxHeartbeats 200000 in
-- Preserve the original budget for the full native mapping or Kan construction.
/-- The actual pointed undercategory has the required native small colimits. -/
theorem hasSmallColimits : HasColimitsOfSize.{0, 0} PointedCGWH.{u, v} := by
  let _ : HasColimitsOfSize.{v, v} PointedCGWH.{u, v} := inferInstance
  exact hasColimitsOfSizeShrink.{0, 0} PointedCGWH.{u, v}

attribute [local instance] hasSmallColimits

variable {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]
  (W : EnrichedFunctor PointedCGWH.{u, v} Iᵒᵖ PointedCGWH.{u, v})
  (X : EnrichedFunctor PointedCGWH.{u, v} I PointedCGWH.{u, v})

set_option maxHeartbeats 200000 in
-- Preserve the original budget for the full native mapping or Kan construction.
/-- The original tensor-object coproduct exists at the actual bare index size. -/
theorem hasObjectCoproduct : HasCoproduct (Enriched.weightedCoend.objects W X) :=
  inferInstance

set_option maxHeartbeats 200000 in
-- Preserve the original budget for the full native mapping or Kan construction.
/-- Each relation retains its full enriched Hom tensor and the original ordered pair of indices. -/
theorem hasRelationCoproduct : HasCoproduct (Enriched.weightedCoend.relations W X) :=
  inferInstance

set_option maxHeartbeats 200000 in
-- Preserve the original budget for the full native mapping or Kan construction.
/-- The actual parallel balancing maps have their native coequalizer. -/
theorem hasBalancingCoequalizer : HasCoequalizer
    (Enriched.weightedCoend.leftMap W X) (Enriched.weightedCoend.rightMap W X) :=
  inferInstance

set_option maxHeartbeats 200000 in
-- Preserve the original budget for the full native mapping or Kan construction.
/-- The original weighted coend is computed with the proved native colimit witnesses. -/
abbrev coend : PointedCGWH.{u, v} := Enriched.weightedCoend W X

end PointedCGWH.EnrichedKan
