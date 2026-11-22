/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentUnstraighteningFibre
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentUnstraighteningMarked
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentSharpSection

/-!
# Exact original sharp marked section fibres

Over a fixed original coherent base edge, the marked unstraightening
edge condition is exactly the original coefficient-edge marking.
The proved sharp-cone criterion therefore identifies the actual whole
fibre with sharp marked sections, with no replacement of its base,
edge or section data.
-/

noncomputable section
universe u
open CategoryTheory

namespace SSet.Marked.CoherentWeight

attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

variable {C : Type u} [EnrichedCategory SSet.{u} C]

/-- The actual marked fibre over the original coherent edge is precisely its entire sharp-cone section Hom. -/
def fixedSharpSectionEquiv (F : EnrichedDiagram Cᵒᵖ)
    (σ : EnrichedFunctor SSet.{u} (Index.{u} 1) C) :
    {a : {e : UnstraighteningSimplex F 1 // e.base = σ} //
      a.val ∈ (coherentUnstraightening C F).marking} ≃
        EnrichedDiagramMap (sharpConeDiagram 1) (simplexCoefficient F σ) :=
  (Equiv.subtypeEquiv (fixedSectionEquiv F σ) (fun a => by
    rcases a with ⟨⟨σ', a⟩, h⟩
    cases h
    rfl)).trans (sharpSectionEquiv (simplexCoefficient F σ)).symm

end SSet.Marked.CoherentWeight
