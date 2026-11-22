/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentUnstraightening
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeEdge

/-!
# The actual marking of coherent unstraightening

An original unstraightening edge is marked exactly when its original
coefficient edge at vertex zero is marked. The whole base simplex and
every cone operator remain unchanged. Original degeneracies are marked
because their cone image has constant maximum. This constructs the
native marked carrier and projection; fibrancy and derived equivalence
are separate statements to prove.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight

attribute [local instance] markedSimplicialCategory enrichedDiagramCategory vertexDecidableEq

variable (C : Type u) [EnrichedCategory SSet.{u} C]

/-- The native unstraightening marking reads the actual original coefficient edge at vertex zero. -/
def coherentUnstraightening (F : EnrichedDiagram Cᵒᵖ) : Marked.{u} where
  toSSet := unstraighteningCore C F
  marking := {e | (e.sectionMap.app (op (SimplicialThickening.mk zeroOne))).hom.app (op ⦋1⦌)
      coefficientEdge ∈ (F.obj (op (e.base.obj (SimplicialThickening.mk zeroOne)))).marking}
  degenerate_mem a := by
    let f := (SimplexCategory.σ (0 : Fin 1)).toOrderHom.uliftMap
    let i : Index.{u} 1 := SimplicialThickening.mk zeroOne
    change (a.sectionMap.app (op ((indexMap f).obj i))).hom.app (op ⦋1⦌)
        ((coneImage f zeroOne).hom.app (op ⦋1⦌) coefficientEdge) ∈
      (F.obj (op (a.base.obj ((indexMap f).obj i)))).marking
    exact (a.sectionMap.app (op ((indexMap f).obj i))).preserve (coefficientEdge_image_zero f)

/-- The original marked base projection retains precisely the same whole coherent simplex. -/
def coherentUnstraighteningProjection (F : EnrichedDiagram Cᵒᵖ) :
    coherentUnstraightening C F ⟶ max (coherentBase C) :=
  toMax (unstraighteningProjection C F)

/-- The designated edge condition is exactly the original coefficient marking, with no replacement or certificate. -/
theorem coherentUnstraightening_marking (F : EnrichedDiagram Cᵒᵖ)
    (e : (unstraighteningCore C F) _⦋1⦌) :
    e ∈ (coherentUnstraightening C F).marking ↔
      (e.sectionMap.app (op (SimplicialThickening.mk zeroOne))).hom.app (op ⦋1⦌) coefficientEdge ∈
        (F.obj (op (e.base.obj (SimplicialThickening.mk zeroOne)))).marking := Iff.rfl

/-- Every original base operator of the marked projection is the unchanged coherent simplex operator. -/
theorem coherentUnstraighteningProjection_hom (F : EnrichedDiagram Cᵒᵖ) :
    (coherentUnstraighteningProjection C F).hom = unstraighteningProjection C F := rfl

end SSet.Marked.CoherentWeight
