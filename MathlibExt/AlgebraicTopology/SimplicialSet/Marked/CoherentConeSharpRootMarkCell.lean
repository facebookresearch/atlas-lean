/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentSharpCone
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeRootValueIso
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.EnrichedFreeMarkedCofibrations
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.Iso

/-!
# The original sharp interval root marking cell

The sharp interval retains the entire original cone-subset nerves and
path actions. Its root coefficient gains the original crossing edge
mark; the same actual coefficient map has its genuine free extension.
The original free/evaluation unit proves the whole enriched cell square,
and its underlying identity is a genuine marked coefficient mono.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory vertexDecidableEq

/-- The full original root marking map of the sharp interval is the unchanged underlying coefficient identity with
the target's original maximal marking. -/
def coneSharpRootMarkCell : coneWeight (⊥ : Vertex.{u} 1) ⟶ max (coneWeight (⊥ : Vertex.{u} 1)).toSSet :=
  (coneSharp 1).app (op (SimplicialThickening.mk (⊥ : Vertex.{u} 1)))

/-- The unchanged original root marking cell is genuinely monic on its whole simplicial carrier. -/
instance coneSharpRootMarkCell_mono : Mono coneSharpRootMarkCell.{u} :=
  (mono_iff_underlying _).mpr (inferInstance : Mono (𝟙 (coneWeight (⊥ : Vertex.{u} 1)).toSSet))

/-- The same actual original root marking cell has its full native free marked extension. -/
def coneSharpRootMarkFreeMap :
    enrichedFreeDiagram (Index.{u} 1)ᵒᵖ (op (SimplicialThickening.mk (⊥ : Vertex.{u} 1)))
      (coneWeight (⊥ : Vertex.{u} 1)) ⟶
    enrichedFreeDiagram (Index.{u} 1)ᵒᵖ (op (SimplicialThickening.mk (⊥ : Vertex.{u} 1)))
      (max (coneWeight (⊥ : Vertex.{u} 1)).toSSet) :=
  (enrichedFreeDiagramFunctor (Index.{u} 1)ᵒᵖ
    (op (SimplicialThickening.mk (⊥ : Vertex.{u} 1)))).map coneSharpRootMarkCell

/-- The original sharp root coefficient extends by its actual identity into the same entire sharp interval diagram. -/
def coneSharpRootFreeLeg :
    enrichedFreeDiagram (Index.{u} 1)ᵒᵖ (op (SimplicialThickening.mk (⊥ : Vertex.{u} 1)))
      (max (coneWeight (⊥ : Vertex.{u} 1)).toSSet) ⟶ sharpConeDiagram 1 :=
  enrichedFreeExtend (Index.{u} 1)ᵒᵖ (op (SimplicialThickening.mk (⊥ : Vertex.{u} 1)))
    (max (coneWeight (⊥ : Vertex.{u} 1)).toSSet) (sharpConeDiagram 1) (𝟙 _)

/-- The genuine full sharp root free leg reads precisely the original coefficient identity under the actual
free/evaluation unit. -/
theorem coneSharpRootFreeLeg_unit :
    enrichedFreeUnit (Index.{u} 1)ᵒᵖ (op (SimplicialThickening.mk (⊥ : Vertex.{u} 1)))
      (max (coneWeight (⊥ : Vertex.{u} 1)).toSSet) ≫
        coneSharpRootFreeLeg.app (op (SimplicialThickening.mk (⊥ : Vertex.{u} 1))) = 𝟙 _ :=
  enrichedFreeExtend_unit (Index.{u} 1)ᵒᵖ (op (SimplicialThickening.mk (⊥ : Vertex.{u} 1)))
    (max (coneWeight (⊥ : Vertex.{u} 1)).toSSet) (sharpConeDiagram 1) (𝟙 _)

/-- The unchanged original root marking map and free coefficient identities form the actual entire sharp interval
enriched cell square. -/
theorem coneSharpRootMark_condition :
    coneSharpRootMarkFreeMap.{u} ≫ coneSharpRootFreeLeg = coneRootFreeMap 1 ≫ coneSharp 1 := by
  let C := (Index.{u} 1)ᵒᵖ
  let c := op (SimplicialThickening.mk (⊥ : Vertex.{u} 1))
  let A := coneWeight (⊥ : Vertex.{u} 1)
  let D := max A.toSSet
  apply (enrichedFreeHomEquiv C c A (sharpConeDiagram 1)).injective
  have hl := (enrichedFreeEvaluationAdjunction C c).homEquiv_naturality_left
    coneSharpRootMarkCell coneSharpRootFreeLeg
  have hr := (enrichedFreeEvaluationAdjunction C c).homEquiv_naturality_right (coneRootFreeMap 1) (coneSharp 1)
  change enrichedFreeUnit C c A ≫ (coneSharpRootMarkFreeMap ≫ coneSharpRootFreeLeg).app c =
    coneSharpRootMarkCell ≫ (enrichedFreeUnit C c D ≫ coneSharpRootFreeLeg.app c) at hl
  change enrichedFreeUnit C c A ≫ (coneRootFreeMap 1 ≫ coneSharp 1).app c =
    (enrichedFreeUnit C c A ≫ (coneRootFreeMap 1).app c) ≫ coneSharpRootMarkCell at hr
  rw [coneSharpRootFreeLeg_unit] at hl
  rw [coneRootFreeMap_unit] at hr
  exact hl.trans ((Category.comp_id _).trans ((Category.id_comp _).symm.trans hr.symm))

/-- The same original free root marking cell has the genuine projective left class through its actual whole marked
coefficient mono. -/
theorem coneSharpRootMarkFreeMap_projectiveLeft :
    (enrichedFreeGenerators (Index.{u} 1)ᵒᵖ coefficientGeneratingMonos).rlp.llp coneSharpRootMarkFreeMap.{u} :=
  enrichedFree_markedMono_left (Index.{u} 1)ᵒᵖ (op (SimplicialThickening.mk (⊥ : Vertex.{u} 1)))
    coneSharpRootMarkCell

end SSet.Marked.CoherentWeight
