/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeAfterMonomorphism
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentFreeSelfValueIso
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.EnrichedFreeMarkedCofibrations

/-!
# Actual original free root attachment maps

The full positive-maximum coefficient at the original root includes
monically into its whole cone coefficient. Its genuine free diagram map
is therefore projectively cofibrant. The original free identity maps
enter the positive subdiagram and the whole cone, retaining every whole
Hom action and the original unit evaluation. The attachment square is
proved by the native free/evaluation adjunction, without a relative
pushout or model-class outcome premise.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory vertexDecidableEq

/-- The actual original root coefficient-boundary free map. -/
def coneRootBoundaryFreeMap (n : ℕ) :
    enrichedFreeDiagram (Index.{u} n)ᵒᵖ (op (SimplicialThickening.mk (⊥ : Vertex.{u} n)))
        (coneAfterWeight (⊥ : Vertex.{u} n) ⊥) ⟶
      enrichedFreeDiagram (Index.{u} n)ᵒᵖ (op (SimplicialThickening.mk (⊥ : Vertex.{u} n))) (coneWeight (⊥ :
        Vertex.{u} n)) :=
  (enrichedFreeDiagramFunctor (Index.{u} n)ᵒᵖ (op (SimplicialThickening.mk (⊥ : Vertex.{u} n)))).map
    (coneAfterInclusion (⊥ : Vertex.{u} n) ⊥)

/-- The whole original positive-maximum root coefficient has its genuine free identity extension into the
  actual positive-maximum subdiagram. -/
def coneAfterRootFreeMap (n : ℕ) :
    enrichedFreeDiagram (Index.{u} n)ᵒᵖ (op (SimplicialThickening.mk (⊥ : Vertex.{u} n)))
      (coneAfterWeight (⊥ : Vertex.{u} n) ⊥) ⟶ coneAfterDiagram (⊥ : Vertex.{u} n) :=
  enrichedFreeExtend _ _ _ _ (𝟙 _)

/-- The entire original root cone coefficient has its same native free identity extension into the whole
  original cone. -/
def coneRootFreeMap (n : ℕ) :
    enrichedFreeDiagram (Index.{u} n)ᵒᵖ (op (SimplicialThickening.mk (⊥ : Vertex.{u} n)))
      (coneWeight (⊥ : Vertex.{u} n)) ⟶ coneDiagram n :=
  enrichedFreeExtend _ _ _ _ (𝟙 _)

/-- The actual original root free-boundary map has the full projective marked left class. -/
theorem coneRootBoundaryFreeMap_projectiveLeft (n : ℕ) :
    (enrichedFreeGenerators (Index.{u} n)ᵒᵖ coefficientGeneratingMonos).rlp.llp (coneRootBoundaryFreeMap.{u} n) :=
  enrichedFree_markedMono_left (Index.{u} n)ᵒᵖ (op (SimplicialThickening.mk (⊥ : Vertex.{u} n)))
    (coneAfterInclusion (⊥ : Vertex.{u} n) ⊥)

/-- Original native unit evaluation of the positive-maximum root extension is the entire unchanged
  coefficient identity. -/
theorem coneAfterRootFreeMap_unit (n : ℕ) :
    enrichedFreeUnit (Index.{u} n)ᵒᵖ (op (SimplicialThickening.mk (⊥ : Vertex.{u} n))) (coneAfterWeight (⊥ :
      Vertex.{u} n) ⊥) ≫
      (coneAfterRootFreeMap n).app (op (SimplicialThickening.mk (⊥ : Vertex.{u} n))) = 𝟙 _ :=
  enrichedFreeExtend_unit (Index.{u} n)ᵒᵖ (op (SimplicialThickening.mk (⊥ : Vertex.{u} n)))
    (coneAfterWeight (⊥ : Vertex.{u} n) ⊥) (coneAfterDiagram (⊥ : Vertex.{u} n)) (𝟙 _)

/-- Original native unit evaluation of the whole root cone extension is the entire actual coefficient identity. -/
theorem coneRootFreeMap_unit (n : ℕ) :
    enrichedFreeUnit (Index.{u} n)ᵒᵖ (op (SimplicialThickening.mk (⊥ : Vertex.{u} n))) (coneWeight (⊥ : Vertex.{u} n)) ≫
      (coneRootFreeMap n).app (op (SimplicialThickening.mk (⊥ : Vertex.{u} n))) = 𝟙 _ :=
  enrichedFreeExtend_unit (Index.{u} n)ᵒᵖ (op (SimplicialThickening.mk (⊥ : Vertex.{u} n)))
    (coneWeight (⊥ : Vertex.{u} n)) (coneDiagram n) (𝟙 _)

/-- The entire original free root-boundary square commutes with its actual positive-maximum and full cone inclusions. -/
theorem coneRootCell_condition (n : ℕ) :
    coneRootBoundaryFreeMap.{u} n ≫ coneRootFreeMap n =
      coneAfterRootFreeMap n ≫ coneAfterDiagramInclusion (⊥ : Vertex.{u} n) := by
  let c := op (SimplicialThickening.mk (⊥ : Vertex.{u} n))
  let A := coneAfterWeight (⊥ : Vertex.{u} n) ⊥
  apply (enrichedFreeHomEquiv (Index.{u} n)ᵒᵖ c A (coneDiagram n)).injective
  have hl := (enrichedFreeEvaluationAdjunction (Index.{u} n)ᵒᵖ c).homEquiv_naturality_left
    (coneAfterInclusion (⊥ : Vertex.{u} n) ⊥) (coneRootFreeMap n)
  have hr := (enrichedFreeEvaluationAdjunction (Index.{u} n)ᵒᵖ c).homEquiv_naturality_right
    (coneAfterRootFreeMap n) (coneAfterDiagramInclusion (⊥ : Vertex.{u} n))
  change enrichedFreeUnit _ c A ≫ (coneRootBoundaryFreeMap n ≫ coneRootFreeMap n).app c =
    coneAfterInclusion (⊥ : Vertex.{u} n) ⊥ ≫
      (enrichedFreeUnit _ c (coneWeight (⊥ : Vertex.{u} n)) ≫ (coneRootFreeMap n).app c) at hl
  change enrichedFreeUnit _ c A ≫ (coneAfterRootFreeMap n ≫ coneAfterDiagramInclusion (⊥ : Vertex.{u} n)).app c =
    (enrichedFreeUnit _ c A ≫ (coneAfterRootFreeMap n).app c) ≫ coneAfterInclusion (⊥ : Vertex.{u} n) ⊥ at hr
  rw [coneRootFreeMap_unit] at hl
  rw [coneAfterRootFreeMap_unit] at hr
  exact hl.trans ((Category.comp_id _).trans ((Category.id_comp _).symm.trans hr.symm))

end SSet.Marked.CoherentWeight
