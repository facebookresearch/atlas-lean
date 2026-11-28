/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.EnrichedColimit

/-!
# Small colimits of genuine marked enriched diagrams

The actual marked carrier has all coefficient-sized colimits. The
proved whole pointwise universal property therefore constructs those
colimits for marked-valued enriched diagrams, while the source-object
universe remains independent. The named proof is not registered as a
new global category or model instance.
-/

noncomputable section
universe u v
open CategoryTheory Limits

namespace SSet.Marked.EnrichedColimit

attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- Actual coefficient-sized marked colimits give all whole enriched diagram colimits at the same size. -/
theorem hasColimits (C : Type v) [EnrichedCategory SSet.{u} C] :
    HasColimitsOfSize.{u, u} (EnrichedDiagram C) where
  has_colimits_of_shape J _ :=
    { has_colimit K := by
        let _ : ∀ x : C, HasColimit (evaluated K x) := fun _ => inferInstance
        exact hasColimit K }

end SSet.Marked.EnrichedColimit
