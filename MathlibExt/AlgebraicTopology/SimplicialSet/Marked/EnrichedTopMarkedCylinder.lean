/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.TopMarkedCylinderEnrichment

/-!
# Actual top-marked cylinders of whole marked enriched diagrams

Postcomposition with the constructed enriched cylinder retains every
original source object, whole Hom action and natural marked component
map. The exact old coefficient and interval coordinates remain in the
original cylinder; the entire top layer is marked as constructed.
No projective cofibration or model-equivalence outcome is assumed.
-/

noncomputable section
universe u v
open CategoryTheory Opposite

namespace SSet.Marked
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- The original top-marked enriched cylinder acts on every whole native marked diagram and full natural map. -/
def enrichedDiagramTopMarkedCylinder (C : Type v) [EnrichedCategory SSet.{u} C] :
    EnrichedDiagram C ⥤ EnrichedDiagram C where
  obj F := F.comp SSet.{u} topMarkedCylinderEnriched
  map {F G} α :=
    { app x := topMarkedCylinderMap (α.app x)
      naturality x y := by
        ext n f
        apply Hom.ext
        ext q z
        have h := congr($(α.naturality x y).app n f)
        have hp := congrArg (fun a => a.hom.app q (z.1, z.2.1)) h
        exact Prod.ext hp rfl }
  map_id F := by
    apply EnrichedDiagramMap.ext
    funext x
    apply Hom.ext
    rfl
  map_comp α β := by
    apply EnrichedDiagramMap.ext
    funext x
    apply Hom.ext
    rfl

/-- Each original source object keeps the actual explicitly marked coefficient cylinder, with no alternate carrier. -/
theorem enrichedDiagramTopMarkedCylinder_obj (C : Type v) [EnrichedCategory SSet.{u} C]
    (F : EnrichedDiagram C) (x : C) :
    ((enrichedDiagramTopMarkedCylinder C).obj F).obj x = topMarkedCylinder (F.obj x) := rfl

/-- Whole natural component maps are exactly their original top-marked coefficient cylinder maps. -/
theorem enrichedDiagramTopMarkedCylinder_map (C : Type v) [EnrichedCategory SSet.{u} C]
    {F G : EnrichedDiagram C} (α : F ⟶ G) (x : C) :
    ((enrichedDiagramTopMarkedCylinder C).map α).app x = topMarkedCylinderMap (α.app x) := rfl

end SSet.Marked
