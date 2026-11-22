/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Enriched.Limits.WeightedEnd
public import MathlibExt.Topology.Category.PointedCGWH.Closed
public import MathlibExt.Topology.Category.CGWH.Limits
public import Mathlib.CategoryTheory.Limits.Comma

/-!
# Actual native small mapping ends

Native pointed limits of size (v,v) supply limits of size (0,0) by the
actual size-shrink witness. The full object/relation products and equalizer
therefore exist for every genuine native enriched source of type zero.
The particular end witnesses are outputs, rather than caller assumptions.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits
open scoped CGWH.limits MonoidalClosed

namespace PointedCGWH.EnrichedMapping

attribute [local instance] MonoidalClosed.enrichedCategorySelf

set_option maxHeartbeats 200000 in
-- Preserve the original budget for the full native mapping or Kan construction.
/-- The actual generic undercategory limits supply native limits of size (0,0). -/
theorem hasSmallLimits : HasLimitsOfSize.{0, 0} PointedCGWH.{u, v} := by
  let _ : HasLimitsOfSize.{v, v} PointedCGWH.{u, v} := inferInstance
  exact hasLimitsOfSizeShrink.{0, 0} PointedCGWH.{u, v}

attribute [local instance] hasSmallLimits

variable {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]
  (W F : EnrichedFunctor PointedCGWH.{u, v} I PointedCGWH.{u, v})

set_option maxHeartbeats 200000 in
-- Preserve the original budget for the full native mapping or Kan construction.
/-- The full native internal-Hom object product exists without a particular-end input. -/
theorem hasObjectProduct : HasProduct (Enriched.weightedEnd.objects W F) :=
  inferInstance

set_option maxHeartbeats 200000 in
-- Preserve the original budget for the full native mapping or Kan construction.
/-- The full native enriched-Hom relation product exists at the original index size. -/
theorem hasRelationProduct : HasProduct (Enriched.weightedEnd.relations W F) :=
  inferInstance

set_option maxHeartbeats 200000 in
-- Preserve the original budget for the full native mapping or Kan construction.
/-- The actual native parallel naturality maps have their required equalizer. -/
theorem hasMappingEqualizer : HasEqualizer
    (Enriched.weightedEnd.leftMap W F) (Enriched.weightedEnd.rightMap W F) :=
  inferInstance

set_option maxHeartbeats 200000 in
-- Preserve the original budget for the full native mapping or Kan construction.
/-- The full native weighted end uses the actual small native limit witnesses. -/
abbrev mappingEnd : PointedCGWH.{u, v} := Enriched.weightedEnd W F

end PointedCGWH.EnrichedMapping
