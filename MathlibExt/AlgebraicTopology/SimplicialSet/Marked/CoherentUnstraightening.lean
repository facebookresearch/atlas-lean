/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentUnstraighteningSimplex

/-!
# The genuine coherent unstraightening simplicial carrier

Every simplex is its original coherent base simplex together with the
whole maximum-marked cone section. All faces and degeneracies are the
proved original ordinal restrictions. The base projection retains the
same full coherent simplex. This constructs the actual simplicial
carrier and maps, without a target-model or Quillen-equivalence premise.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight

attribute [local instance] markedSimplicialCategory enrichedDiagramCategory vertexDecidableEq

variable (C : Type u) [EnrichedCategory SSet.{u} C]

/-- The original coherent nerve of the supplied enriched base, with its unchanged vertices and Hom data. -/
abbrev coherentBase : SSet.{u} := SimplicialNerve (ForgetEnrichment SSet.{u} C)

/-- The actual coherent unstraightening carrier retains all original base and marked section simplices. -/
def unstraighteningCore (F : EnrichedDiagram Cᵒᵖ) : SSet.{u} where
  obj n := UnstraighteningSimplex F n.unop.len
  map f := ↾fun a => a.pull f.unop.toOrderHom.uliftMap
  map_id n := by
    ext a
    exact UnstraighteningSimplex.pull_id a
  map_comp f g := by
    ext a
    exact (UnstraighteningSimplex.pull_comp f.unop.toOrderHom.uliftMap
      g.unop.toOrderHom.uliftMap a).symm

/-- The genuine projection keeps the entire original coherent base simplex, in every degree. -/
def unstraighteningProjection (F : EnrichedDiagram Cᵒᵖ) : unstraighteningCore C F ⟶ coherentBase C where
  app n := ↾fun a => a.base
  naturality n m f := rfl

/-- All original unstraightening simplex operators use exactly the proved whole cone restrictions. -/
theorem unstraighteningCore_map (F : EnrichedDiagram Cᵒᵖ) {n m : SimplexCategoryᵒᵖ}
    (f : n ⟶ m) (a : (unstraighteningCore C F).obj n) :
    (unstraighteningCore C F).map f a = a.pull f.unop.toOrderHom.uliftMap := rfl

/-- The base projection retains precisely the whole original enriched simplex, without a replacement. -/
theorem unstraighteningProjection_app (F : EnrichedDiagram Cᵒᵖ) (n : ℕ)
    (a : UnstraighteningSimplex F n) :
    (unstraighteningProjection C F).app (op ⦋n⦌) a = a.base := rfl

end SSet.Marked.CoherentWeight
