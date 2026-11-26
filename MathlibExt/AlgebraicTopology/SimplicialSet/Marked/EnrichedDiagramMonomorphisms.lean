/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.EnrichedDiagram

/-!
# Whole enriched monomorphisms from original coefficient monomorphisms

Full enriched maps are determined by their original coefficient
maps. Their genuine coefficient monomorphisms therefore give a
whole enriched monomorphism. This is a named proof, rather than a
new global category or model instance.
-/

noncomputable section
universe u v
open CategoryTheory

namespace SSet.Marked
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- Actual monomorphisms at every original coefficient give a monomorphism of the same whole enriched map. -/
theorem enrichedDiagramMap_mono_of_components {C : Type v} [EnrichedCategory SSet.{u} C]
    {F G : EnrichedDiagram C} (α : F ⟶ G) (h : ∀ x : C, Mono (α.app x)) : Mono α where
  right_cancellation f g w := by
    apply EnrichedDiagramMap.ext
    funext x
    let _ : Mono (α.app x) := h x
    exact (cancel_mono (α.app x)).mp (congrArg (fun a => a.app x) w)

end SSet.Marked
