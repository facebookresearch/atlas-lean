/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeCriticalEdgeRepresentatives
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeCriticalHornDiagram
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeSharpRootMarkCell

/-!
# The original critical predecessor free marking cell and both whole squares

The SAME interval root marking cell is freed at the original critical
predecessor. Its coefficient maps are the full original critical edge
operator into the original cone and horn. Their actual free-evaluation
units prove both complete enriched squares. All whole original actions
and the unchanged original horn inclusion are retained.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory vertexDecidableEq

/-- The original interval root enters the whole original cone along the exact original critical edge. -/
def coneCriticalEdgeMinimalRoot (n : ℕ) :
    coneWeight (⊥ : Vertex.{u} 1) ⟶ coneWeight (coneCriticalPrevious n) :=
  coneImage (coneCriticalEdgeOrder n) (⊥ : Vertex.{u} 1)

/-- The SAME original interval root with maximal marking enters precisely the critical coefficient marking. -/
def coneCriticalEdgeSharpRoot (n : ℕ) :
    max (coneWeight (⊥ : Vertex.{u} 1)).toSSet ⟶ coneCriticalWeight n (coneCriticalPrevious n) where
  hom := (coneCriticalEdgeMinimalRoot n).hom
  preserve {e} _ := by
    change coneCriticalMaximumCollapse n ((e.obj 0).image (coneCriticalEdgeOrder n)).maximum =
      coneCriticalMaximumCollapse n ((e.obj 1).image (coneCriticalEdgeOrder n)).maximum
    rw [ConeSubset.image_maximum, ConeSubset.image_maximum]
    exact (coneCriticalEdgeOrder_collapsed n (e.obj 0).maximum).trans
      (coneCriticalEdgeOrder_collapsed n (e.obj 1).maximum).symm

/-- The same full original supported horn gains its critical marks by its literal underlying identity. -/
def coneCriticalHornDiagramMark (n : ℕ) :
    coneRootHornDiagram.{u} (Fin.last (n + 2)) ⟶ coneCriticalHornDiagram n where
  app i :=
    { hom := 𝟙 _
      preserve he := congrArg (coneCriticalMaximumCollapse n) he }
  naturality i j := by
    ext q p
    apply Hom.ext
    ext r a
    rfl

/-- Both original marked horn inclusions retain the SAME whole marking square. -/
theorem coneCriticalHornDiagramMark_inclusion (n : ℕ) :
    coneCriticalHornDiagramMark.{u} n ≫ coneCriticalHornInclusion n =
      coneRootHornDiagramInclusion (Fin.last (n + 2)) ≫ coneCriticalDiagramMark n := by
  apply EnrichedDiagramMap.ext
  funext i
  exact Hom.ext rfl

/-- The original whole critical edge enters the SAME original minimal horn at its positive predecessor. -/
def coneCriticalEdgeMinimalHornRoot (n : ℕ) :
    coneWeight (⊥ : Vertex.{u} 1) ⟶ coneRootHornMarked (Fin.last (n + 2)) (coneCriticalPrevious n) :=
  coneCriticalEdgeMinimalRoot n ≫ (coneRootHornAboveIso (Fin.last (n + 2)) (coneCriticalPrevious_pos n)).inv

/-- The SAME original sharp critical edge enters the entire critically marked horn at that predecessor. -/
def coneCriticalEdgeSharpHornRoot (n : ℕ) :
    max (coneWeight (⊥ : Vertex.{u} 1)).toSSet ⟶ coneCriticalHornWeight n (coneCriticalPrevious n) :=
  coneCriticalEdgeSharpRoot n ≫ (coneCriticalHornAboveIso n (coneCriticalPrevious_pos n)).inv

/-- The whole original cone coefficient marking square uses exactly the same original interval root cell. -/
theorem coneCriticalEdgeConeRoot_condition (n : ℕ) :
    coneSharpRootMarkCell ≫ coneCriticalEdgeSharpRoot n =
      coneCriticalEdgeMinimalRoot n ≫
        (coneCriticalDiagramMark n).app (op (SimplicialThickening.mk (coneCriticalPrevious.{u} n))) :=
  Hom.ext rfl

/-- The entire original horn coefficient marking square retains the same original interval cell and upper support. -/
theorem coneCriticalEdgeHornRoot_condition (n : ℕ) :
    coneSharpRootMarkCell ≫ coneCriticalEdgeSharpHornRoot n =
      coneCriticalEdgeMinimalHornRoot n ≫
        (coneCriticalHornDiagramMark n).app (op (SimplicialThickening.mk (coneCriticalPrevious.{u} n))) :=
  Hom.ext rfl

/-- The SAME actual original interval root marking cell is freed at the actual critical predecessor. -/
def coneCriticalEdgeFreeMap (n : ℕ) :
    enrichedFreeDiagram (Index.{u} (n + 2))ᵒᵖ (op (SimplicialThickening.mk (coneCriticalPrevious n)))
      (coneWeight (⊥ : Vertex.{u} 1)) ⟶
    enrichedFreeDiagram (Index.{u} (n + 2))ᵒᵖ (op (SimplicialThickening.mk (coneCriticalPrevious n)))
      (max (coneWeight (⊥ : Vertex.{u} 1)).toSSet) :=
  (enrichedFreeDiagramFunctor (Index.{u} (n + 2))ᵒᵖ
    (op (SimplicialThickening.mk (coneCriticalPrevious n)))).map coneSharpRootMarkCell

/-- The original critical edge extends into the entire original minimally marked cone by its genuine whole action. -/
def coneCriticalEdgeConeMinimalLeg (n : ℕ) :
    enrichedFreeDiagram (Index.{u} (n + 2))ᵒᵖ (op (SimplicialThickening.mk (coneCriticalPrevious n)))
      (coneWeight (⊥ : Vertex.{u} 1)) ⟶ coneDiagram (n + 2) :=
  enrichedFreeExtend (Index.{u} (n + 2))ᵒᵖ (op (SimplicialThickening.mk (coneCriticalPrevious n)))
    (coneWeight (⊥ : Vertex.{u} 1)) (coneDiagram (n + 2)) (coneCriticalEdgeMinimalRoot n)

/-- The SAME sharp edge extends into the whole original critically marked cone by its actual whole action. -/
def coneCriticalEdgeConeSharpLeg (n : ℕ) :
    enrichedFreeDiagram (Index.{u} (n + 2))ᵒᵖ (op (SimplicialThickening.mk (coneCriticalPrevious n)))
      (max (coneWeight (⊥ : Vertex.{u} 1)).toSSet) ⟶ coneCriticalDiagram n :=
  enrichedFreeExtend (Index.{u} (n + 2))ᵒᵖ (op (SimplicialThickening.mk (coneCriticalPrevious n)))
    (max (coneWeight (⊥ : Vertex.{u} 1)).toSSet) (coneCriticalDiagram n) (coneCriticalEdgeSharpRoot n)

/-- The original critical edge extends into the SAME full original minimally marked terminal horn. -/
def coneCriticalEdgeHornMinimalLeg (n : ℕ) :
    enrichedFreeDiagram (Index.{u} (n + 2))ᵒᵖ (op (SimplicialThickening.mk (coneCriticalPrevious n)))
      (coneWeight (⊥ : Vertex.{u} 1)) ⟶ coneRootHornDiagram (Fin.last (n + 2)) :=
  enrichedFreeExtend (Index.{u} (n + 2))ᵒᵖ (op (SimplicialThickening.mk (coneCriticalPrevious n)))
    (coneWeight (⊥ : Vertex.{u} 1)) (coneRootHornDiagram (Fin.last (n + 2))) (coneCriticalEdgeMinimalHornRoot n)

/-- The SAME whole sharp edge extends into the full critically marked terminal horn. -/
def coneCriticalEdgeHornSharpLeg (n : ℕ) :
    enrichedFreeDiagram (Index.{u} (n + 2))ᵒᵖ (op (SimplicialThickening.mk (coneCriticalPrevious n)))
      (max (coneWeight (⊥ : Vertex.{u} 1)).toSSet) ⟶ coneCriticalHornDiagram n :=
  enrichedFreeExtend (Index.{u} (n + 2))ᵒᵖ (op (SimplicialThickening.mk (coneCriticalPrevious n)))
    (max (coneWeight (⊥ : Vertex.{u} 1)).toSSet) (coneCriticalHornDiagram n) (coneCriticalEdgeSharpHornRoot n)

/-- The entire original minimal cone leg reads its SAME whole critical edge under the actual unit. -/
theorem coneCriticalEdgeConeMinimalLeg_unit (n : ℕ) :
    enrichedFreeUnit (Index.{u} (n + 2))ᵒᵖ (op (SimplicialThickening.mk (coneCriticalPrevious n)))
      (coneWeight (⊥ : Vertex.{u} 1)) ≫
        (coneCriticalEdgeConeMinimalLeg n).app (op (SimplicialThickening.mk (coneCriticalPrevious n))) =
          coneCriticalEdgeMinimalRoot n :=
  enrichedFreeExtend_unit (Index.{u} (n + 2))ᵒᵖ (op (SimplicialThickening.mk (coneCriticalPrevious n)))
    (coneWeight (⊥ : Vertex.{u} 1)) (coneDiagram (n + 2)) (coneCriticalEdgeMinimalRoot n)

/-- The SAME sharp cone leg reads its entire original critical edge under the genuine unit. -/
theorem coneCriticalEdgeConeSharpLeg_unit (n : ℕ) :
    enrichedFreeUnit (Index.{u} (n + 2))ᵒᵖ (op (SimplicialThickening.mk (coneCriticalPrevious n)))
      (max (coneWeight (⊥ : Vertex.{u} 1)).toSSet) ≫
        (coneCriticalEdgeConeSharpLeg n).app (op (SimplicialThickening.mk (coneCriticalPrevious n))) =
          coneCriticalEdgeSharpRoot n :=
  enrichedFreeExtend_unit (Index.{u} (n + 2))ᵒᵖ (op (SimplicialThickening.mk (coneCriticalPrevious n)))
    (max (coneWeight (⊥ : Vertex.{u} 1)).toSSet) (coneCriticalDiagram n) (coneCriticalEdgeSharpRoot n)

/-- The full original minimal horn leg keeps exactly the SAME critical edge under unit evaluation. -/
theorem coneCriticalEdgeHornMinimalLeg_unit (n : ℕ) :
    enrichedFreeUnit (Index.{u} (n + 2))ᵒᵖ (op (SimplicialThickening.mk (coneCriticalPrevious n)))
      (coneWeight (⊥ : Vertex.{u} 1)) ≫
        (coneCriticalEdgeHornMinimalLeg n).app (op (SimplicialThickening.mk (coneCriticalPrevious n))) =
          coneCriticalEdgeMinimalHornRoot n :=
  enrichedFreeExtend_unit (Index.{u} (n + 2))ᵒᵖ (op (SimplicialThickening.mk (coneCriticalPrevious n)))
    (coneWeight (⊥ : Vertex.{u} 1)) (coneRootHornDiagram (Fin.last (n + 2))) (coneCriticalEdgeMinimalHornRoot n)

/-- The SAME full sharp horn leg retains its whole original critical edge under the genuine unit. -/
theorem coneCriticalEdgeHornSharpLeg_unit (n : ℕ) :
    enrichedFreeUnit (Index.{u} (n + 2))ᵒᵖ (op (SimplicialThickening.mk (coneCriticalPrevious n)))
      (max (coneWeight (⊥ : Vertex.{u} 1)).toSSet) ≫
        (coneCriticalEdgeHornSharpLeg n).app (op (SimplicialThickening.mk (coneCriticalPrevious n))) =
          coneCriticalEdgeSharpHornRoot n :=
  enrichedFreeExtend_unit (Index.{u} (n + 2))ᵒᵖ (op (SimplicialThickening.mk (coneCriticalPrevious n)))
    (max (coneWeight (⊥ : Vertex.{u} 1)).toSSet) (coneCriticalHornDiagram n) (coneCriticalEdgeSharpHornRoot n)

/-- The SAME entire original critical cone square is forced by its genuine original free-evaluation unit. -/
theorem coneCriticalEdgeConeFree_condition (n : ℕ) :
    coneCriticalEdgeFreeMap n ≫ coneCriticalEdgeConeSharpLeg n =
      coneCriticalEdgeConeMinimalLeg n ≫ coneCriticalDiagramMark.{u} n := by
  let C := (Index.{u} (n + 2))ᵒᵖ
  let c := op (SimplicialThickening.mk (coneCriticalPrevious.{u} n))
  let A := coneWeight (⊥ : Vertex.{u} 1)
  let D := max A.toSSet
  apply (enrichedFreeHomEquiv C c A (coneCriticalDiagram n)).injective
  have hl := (enrichedFreeEvaluationAdjunction C c).homEquiv_naturality_left
    coneSharpRootMarkCell (coneCriticalEdgeConeSharpLeg n)
  have hr := (enrichedFreeEvaluationAdjunction C c).homEquiv_naturality_right
    (coneCriticalEdgeConeMinimalLeg n) (coneCriticalDiagramMark n)
  change enrichedFreeUnit C c A ≫ (coneCriticalEdgeFreeMap n ≫ coneCriticalEdgeConeSharpLeg n).app c =
    coneSharpRootMarkCell ≫ (enrichedFreeUnit C c D ≫ (coneCriticalEdgeConeSharpLeg n).app c) at hl
  change enrichedFreeUnit C c A ≫ (coneCriticalEdgeConeMinimalLeg n ≫ coneCriticalDiagramMark n).app c =
    (enrichedFreeUnit C c A ≫ (coneCriticalEdgeConeMinimalLeg n).app c) ≫ (coneCriticalDiagramMark n).app c at hr
  rw [coneCriticalEdgeConeSharpLeg_unit] at hl
  rw [coneCriticalEdgeConeMinimalLeg_unit] at hr
  exact hl.trans ((coneCriticalEdgeConeRoot_condition n).trans hr.symm)

/-- The SAME entire original terminal horn square follows from the actual original free-evaluation unit. -/
theorem coneCriticalEdgeHornFree_condition (n : ℕ) :
    coneCriticalEdgeFreeMap n ≫ coneCriticalEdgeHornSharpLeg n =
      coneCriticalEdgeHornMinimalLeg n ≫ coneCriticalHornDiagramMark.{u} n := by
  let C := (Index.{u} (n + 2))ᵒᵖ
  let c := op (SimplicialThickening.mk (coneCriticalPrevious.{u} n))
  let A := coneWeight (⊥ : Vertex.{u} 1)
  let D := max A.toSSet
  apply (enrichedFreeHomEquiv C c A (coneCriticalHornDiagram n)).injective
  have hl := (enrichedFreeEvaluationAdjunction C c).homEquiv_naturality_left
    coneSharpRootMarkCell (coneCriticalEdgeHornSharpLeg n)
  have hr := (enrichedFreeEvaluationAdjunction C c).homEquiv_naturality_right
    (coneCriticalEdgeHornMinimalLeg n) (coneCriticalHornDiagramMark n)
  change enrichedFreeUnit C c A ≫ (coneCriticalEdgeFreeMap n ≫ coneCriticalEdgeHornSharpLeg n).app c =
    coneSharpRootMarkCell ≫ (enrichedFreeUnit C c D ≫ (coneCriticalEdgeHornSharpLeg n).app c) at hl
  change enrichedFreeUnit C c A ≫ (coneCriticalEdgeHornMinimalLeg n ≫ coneCriticalHornDiagramMark n).app c =
    (enrichedFreeUnit C c A ≫ (coneCriticalEdgeHornMinimalLeg n).app c) ≫ (coneCriticalHornDiagramMark n).app c at hr
  rw [coneCriticalEdgeHornSharpLeg_unit] at hl
  rw [coneCriticalEdgeHornMinimalLeg_unit] at hr
  exact hl.trans ((coneCriticalEdgeHornRoot_condition n).trans hr.symm)

end SSet.Marked.CoherentWeight
