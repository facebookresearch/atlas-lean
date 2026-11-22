/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentUnstraighteningSimplex

/-!
# The exact native fibre of a coherent unstraightening simplex

Over a specified original coherent base simplex, the fibre consists
precisely of its whole marked cone sections. Both directions retain
the same base and entire section data; the equality transport is only
the actual original base equation.
-/

noncomputable section
universe u
open CategoryTheory

namespace SSet.Marked.CoherentWeight

attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

variable {C : Type u} [EnrichedCategory SSet.{u} C]

/-- The actual fibre over the original coherent base simplex is its full marked cone-section Hom. -/
def fixedSectionEquiv (F : EnrichedDiagram Cᵒᵖ) {n : ℕ}
    (σ : EnrichedFunctor SSet.{u} (Index.{u} n) C) :
    {a : UnstraighteningSimplex F n // a.base = σ} ≃
      EnrichedDiagramMap (coneDiagram n) (simplexCoefficient F σ) where
  toFun a := a.property ▸ a.val.sectionMap
  invFun a := ⟨⟨σ, a⟩, rfl⟩
  left_inv a := by
    rcases a with ⟨⟨σ', a⟩, h⟩
    cases h
    rfl
  right_inv _ := rfl

end SSet.Marked.CoherentWeight
