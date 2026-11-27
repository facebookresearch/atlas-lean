/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.EnrichedCoproduct

/-!
# The full native Hom correspondence of marked enriched coproducts

The correspondence uses the actual original summand injections and
the proved whole enriched descent. Its inverses retain all marked
components and Hom actions.
-/

noncomputable section
universe u v
open CategoryTheory

namespace SSet.Marked.EnrichedCoproduct

attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

variable {C : Type v} [EnrichedCategory SSet.{u} C] {I : Type u}
    (E : I → EnrichedDiagram C)

/-- Whole original maps from the actual marked enriched coproduct are exactly their full summand maps. -/
def homEquiv (X : EnrichedDiagram C) : (object E ⟶ X) ≃ (∀ i : I, E i ⟶ X) where
  toFun f i := ι E i ≫ f
  invFun := desc E
  left_inv f := by
    apply hom_ext E
    intro i
    exact ι_desc E _ i
  right_inv f := funext (ι_desc E f)

/-- The forward correspondence uses precisely the original summand injection. -/
theorem homEquiv_apply (X : EnrichedDiagram C) (f : object E ⟶ X) (i : I) :
    homEquiv E X f i = ι E i ≫ f := rfl

end SSet.Marked.EnrichedCoproduct
