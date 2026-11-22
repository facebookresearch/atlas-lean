/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeRootBoundaryAfter
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeRootBoundaryValues

/-!
# The actual original positive/free-root boundary square

The complete original positive diagram enters the same supported
root-boundary diagram. At the original root its coefficient inclusion
gives the actual free-root map. Both free legs are the original free
extensions of the unchanged coefficient identities. Their genuine
free/evaluation units give the whole original enriched square.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite

namespace SSet.Marked.CoherentWeight
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory vertexDecidableEq

/-- The complete original positive root coefficient extends into its unchanged original positive diagram by the
actual free/evaluation identity. -/
def conePositiveRootFreeLeg (n : ℕ) :
    enrichedFreeDiagram (Index.{u} n)ᵒᵖ (op (SimplicialThickening.mk (⊥ : Vertex.{u} n)))
      (coneAfterWeight (⊥ : Vertex.{u} n) (⊥ : Vertex.{u} n)) ⟶ coneAfterDiagram (⊥ : Vertex.{u} n) :=
  enrichedFreeExtend _ _ _ _ (𝟙 _)

/-- The same original positive root coefficient enters the complete original marked root-boundary coefficient
through its actual free-root coefficient map. -/
def conePositiveBoundaryFreeMap (n : ℕ) :
    enrichedFreeDiagram (Index.{u} n)ᵒᵖ (op (SimplicialThickening.mk (⊥ : Vertex.{u} n)))
      (coneAfterWeight (⊥ : Vertex.{u} n) (⊥ : Vertex.{u} n)) ⟶
      enrichedFreeDiagram (Index.{u} n)ᵒᵖ (op (SimplicialThickening.mk (⊥ : Vertex.{u} n)))
        (coneRootBoundaryMarked (⊥ : Vertex.{u} n)) :=
  (enrichedFreeDiagramFunctor (Index.{u} n)ᵒᵖ (op (SimplicialThickening.mk (⊥ : Vertex.{u} n)))).map
    (coneRootBoundaryAfterInclusion (⊥ : Vertex.{u} n))

/-- The actual complete original positive free leg has precisely its unchanged original root identity unit. -/
theorem conePositiveRootFreeLeg_unit (n : ℕ) :
    enrichedFreeUnit (Index.{u} n)ᵒᵖ (op (SimplicialThickening.mk (⊥ : Vertex.{u} n)))
      (coneAfterWeight (⊥ : Vertex.{u} n) (⊥ : Vertex.{u} n)) ≫
        (conePositiveRootFreeLeg n).app (op (SimplicialThickening.mk (⊥ : Vertex.{u} n))) = 𝟙 _ :=
  enrichedFreeExtend_unit (Index.{u} n)ᵒᵖ (op (SimplicialThickening.mk (⊥ : Vertex.{u} n)))
    (coneAfterWeight (⊥ : Vertex.{u} n) (⊥ : Vertex.{u} n)) (coneAfterDiagram (⊥ : Vertex.{u} n)) (𝟙 _)

/-- The original positive/free-root square commutes on the entire original marked enriched diagrams and actual
identity free/evaluation units. -/
theorem coneRootBoundaryPositive_condition (n : ℕ) :
    conePositiveBoundaryFreeMap.{u} n ≫ coneRootBoundaryFreeLeg n =
      conePositiveRootFreeLeg n ≫ coneRootBoundaryAfterMap n := by
  let c := op (SimplicialThickening.mk (⊥ : Vertex.{u} n))
  let A := coneAfterWeight (⊥ : Vertex.{u} n) (⊥ : Vertex.{u} n)
  let b := coneRootBoundaryAfterInclusion (⊥ : Vertex.{u} n)
  apply (enrichedFreeHomEquiv (Index.{u} n)ᵒᵖ c A (coneRootBoundaryDiagram n)).injective
  have hl := (enrichedFreeEvaluationAdjunction (Index.{u} n)ᵒᵖ c).homEquiv_naturality_left b (coneRootBoundaryFreeLeg n)
  have hr := (enrichedFreeEvaluationAdjunction (Index.{u} n)ᵒᵖ c).homEquiv_naturality_right
    (conePositiveRootFreeLeg n) (coneRootBoundaryAfterMap n)
  change enrichedFreeUnit _ c A ≫ (conePositiveBoundaryFreeMap n ≫ coneRootBoundaryFreeLeg n).app c =
    b ≫ (enrichedFreeUnit _ c (coneRootBoundaryMarked (⊥ : Vertex.{u} n)) ≫ (coneRootBoundaryFreeLeg n).app c) at hl
  change enrichedFreeUnit _ c A ≫ (conePositiveRootFreeLeg n ≫ coneRootBoundaryAfterMap n).app c =
    (enrichedFreeUnit _ c A ≫ (conePositiveRootFreeLeg n).app c) ≫ b at hr
  rw [coneRootBoundaryFreeLeg_unit] at hl
  rw [conePositiveRootFreeLeg_unit] at hr
  exact hl.trans ((Category.comp_id _).trans ((Category.id_comp _).symm.trans hr.symm))

end SSet.Marked.CoherentWeight
