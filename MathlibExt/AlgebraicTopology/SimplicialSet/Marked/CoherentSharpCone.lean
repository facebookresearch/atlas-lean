/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeDiagram
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.MaximalizationEnrichment

/-!
# The actual sharp coherent cone weight

The sharp weight uses the same original cone-subset nerves and union
actions with their maximal marking. Its original underlying identity
from the maximum-preserving weight is a genuine full enriched natural
map. In the marked simplex/edge presentation this is used for the
original sharp one-simplex; no higher model comparison is assumed.
-/

noncomputable section
universe u
open CategoryTheory Opposite

namespace SSet.Marked.CoherentWeight

attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- The sharp coherent cone keeps the original whole subset nerves and actions while marking all edges. -/
def sharpConeDiagram (n : ℕ) : EnrichedDiagram (Index.{u} n)ᵒᵖ := maximalizedDiagram (coneDiagram n)

/-- The original maximum-preserving cone maps into its sharp weight by the same underlying identities. -/
def coneSharp (n : ℕ) : coneDiagram n ⟶ sharpConeDiagram.{u} n := diagramMaximalization (coneDiagram n)

/-- Every sharp weight component is the same entire original subset nerve with its maximal marking. -/
theorem sharpConeDiagram_value (n : ℕ) (i : Index.{u} n) :
    (sharpConeDiagram n).obj (op i) = max (coneWeight i.as).toSSet := rfl

end SSet.Marked.CoherentWeight
