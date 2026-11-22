/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentUnstraighteningFunctor
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.SmallLimits
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentAdjunction
import Mathlib.CategoryTheory.Comma.Over.Pullback

/-!
# Native marked unstraightening over the original simplicial base

The coherent unstraightening object is pulled back along the actual
coherent-realization unit of the original base. Thus every original
base simplex and its full marked cone data are retained. The selected
pullback, coefficient maps, evaluation projection and whole base
equations are the native categorical maps. No base-fibrancy or model
comparison is required for this carrier construction.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked
open CoherentWeight CategoryTheory.CoherentRealization

attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- The original marked unstraightening functor uses the actual coherent unit and exact native base pullback. -/
def nativeUnstraightening (B : SSet.{u}) :
    EnrichedDiagram (realization B)ᵒᵖ ⥤ Over (max B) :=
  coherentUnstraighteningFunctor (realization B) ⋙ Over.pullback (maximal.map (unit B))

/-- The total object is the original selected marked pullback, with its entire native marking. -/
def nativeUnstraighteningTotal (B : SSet.{u}) (F : EnrichedDiagram (realization B)ᵒᵖ) : Marked.{u} :=
  ((nativeUnstraightening B).obj F).left

/-- The original base projection is the actual second pullback map, with no replacement of the base. -/
def nativeUnstraighteningProjection (B : SSet.{u}) (F : EnrichedDiagram (realization B)ᵒᵖ) :
    nativeUnstraighteningTotal B F ⟶ max B := ((nativeUnstraightening B).obj F).hom

/-- The first native coordinate retains the whole original coherent simplex and marked cone section. -/
def nativeUnstraighteningCoherentProjection (B : SSet.{u}) (F : EnrichedDiagram (realization B)ᵒᵖ) :
    nativeUnstraighteningTotal B F ⟶ coherentUnstraightening (realization B) F :=
  pullback.fst (coherentUnstraighteningProjection (realization B) F) (maximal.map (unit B))

/-- Both original coordinates satisfy precisely the full native unit pullback equation. -/
theorem nativeUnstraightening_pullback_condition (B : SSet.{u}) (F : EnrichedDiagram (realization B)ᵒᵖ) :
    nativeUnstraighteningCoherentProjection B F ≫ coherentUnstraighteningProjection (realization B) F =
      nativeUnstraighteningProjection B F ≫ maximal.map (unit B) := pullback.condition

/-- Every actual coefficient map preserves the whole original base equation after native unstraightening. -/
theorem nativeUnstraightening_map_over (B : SSet.{u}) {F G : EnrichedDiagram (realization B)ᵒᵖ}
    (φ : F ⟶ G) :
    ((nativeUnstraightening B).map φ).left ≫ nativeUnstraighteningProjection B G =
      nativeUnstraighteningProjection B F := Over.w ((nativeUnstraightening B).map φ)

end SSet.Marked
