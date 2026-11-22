/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeCriticalEdgeCharts
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeSharpRootMarkPushout
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Both full original critical interval chart marking pushouts

Actual native free-image units identify the SAME original predecessor
free marking square with left extension of the original interval root
square. The original full interval pushout and whole critical marking
pushout then give both genuine full interval chart pushouts by pasting.
Every original coefficient, critical edge operator and horn inclusion
remains the same actual map; no colimit outcome is a premise.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory vertexDecidableEq

/-- Both actual original free-image inverses retain the SAME unchanged original interval root marking map. -/
theorem coneCriticalEdgeFreeImage_inv_marking (n : ℕ) :
    (enrichedLeftKanFreeIso (coneCriticalEdgeIndex n) (op (SimplicialThickening.mk (⊥ : Vertex.{u} 1)))
      (coneWeight (⊥ : Vertex.{u} 1))).inv ≫
        (EnrichedLeftKan.leftExtension (coneCriticalEdgeIndex n)).map coneSharpRootMarkFreeMap =
      coneCriticalEdgeFreeMap n ≫
        (enrichedLeftKanFreeIso (coneCriticalEdgeIndex n) (op (SimplicialThickening.mk (⊥ : Vertex.{u} 1)))
          (max (coneWeight (⊥ : Vertex.{u} 1)).toSSet)).inv := by
  let C := (Index.{u} 1)ᵒᵖ
  let D := (Index.{u} (n + 2))ᵒᵖ
  let j := coneCriticalEdgeIndex.{u} n
  let c := op (SimplicialThickening.mk (⊥ : Vertex.{u} 1))
  let A := coneWeight (⊥ : Vertex.{u} 1)
  let M := max A.toSSet
  let F := EnrichedLeftKan.object j (enrichedFreeDiagram C c M)
  apply (enrichedFreeHomEquiv D (j.obj c) A F).injective
  have hl := enrichedLeftKanFreeIso_inv_post j c A
    ((EnrichedLeftKan.leftExtension j).map coneSharpRootMarkFreeMap)
  have hm := EnrichedLeftKan.map_homEquiv j coneSharpRootMarkFreeMap
  have hp := enrichedFreeHomEquiv_pre C c coneSharpRootMarkCell
    ((enrichedDiagramRestrict j).obj F) (EnrichedLeftKan.unit j (enrichedFreeDiagram C c M))
  have hr := enrichedFreeHomEquiv_pre D (j.obj c) coneSharpRootMarkCell F (enrichedLeftKanFreeIso j c M).inv
  have he := congrArg (fun f => coneSharpRootMarkCell ≫ f) (enrichedLeftKanFreeIso_inv_unit j c M)
  exact hl.trans ((congrArg (enrichedFreeHomEquiv C c A ((enrichedDiagramRestrict j).obj F)) hm).trans
    (hp.trans (he.symm.trans hr.symm)))

/-- The actual original minimal free-image unit and whole cone mate retain the SAME original predecessor free leg. -/
theorem coneCriticalEdgeFreeImage_inv_coneMinimal (n : ℕ) :
    (enrichedLeftKanFreeIso (coneCriticalEdgeIndex n) (op (SimplicialThickening.mk (⊥ : Vertex.{u} 1)))
      (coneWeight (⊥ : Vertex.{u} 1))).inv ≫
        ((EnrichedLeftKan.leftExtension (coneCriticalEdgeIndex n)).map (coneRootFreeMap 1) ≫
          coneCriticalConeEdgeMap n) = coneCriticalEdgeConeMinimalLeg n := by
  let C := (Index.{u} 1)ᵒᵖ
  let D := (Index.{u} (n + 2))ᵒᵖ
  let j := coneCriticalEdgeIndex.{u} n
  let c := op (SimplicialThickening.mk (⊥ : Vertex.{u} 1))
  let A := coneWeight (⊥ : Vertex.{u} 1)
  apply (enrichedFreeHomEquiv D (j.obj c) A (coneDiagram (n + 2))).injective
  have hl := enrichedLeftKanFreeIso_inv_map_post j c A (coneRootFreeMap 1) (coneCriticalConeEdgeMap n)
  have hm := congrArg (enrichedFreeHomEquiv C c A ((enrichedDiagramRestrict j).obj (coneDiagram (n + 2))))
    (congrArg (fun f => coneRootFreeMap 1 ≫ f) (coneCriticalConeEdgeMap_homEquiv n))
  have hr := enrichedFreeHomEquiv_post C c A (coneRootFreeMap 1) (coneOperator (coneCriticalEdgeOrder n))
  change enrichedFreeHomEquiv C c A _ (coneRootFreeMap 1 ≫ coneOperator (coneCriticalEdgeOrder n)) =
    (enrichedFreeUnit C c A ≫ (coneRootFreeMap 1).app c) ≫ coneCriticalEdgeMinimalRoot n at hr
  rw [coneRootFreeMap_unit] at hr
  exact hl.trans (hm.trans (hr.trans ((Category.id_comp (coneCriticalEdgeMinimalRoot n)).trans
    (coneCriticalEdgeConeMinimalLeg_unit n).symm)))

/-- The SAME actual sharp free-image unit and whole critical cone mate retain the full original sharp predecessor
leg. -/
theorem coneCriticalEdgeFreeImage_inv_coneSharp (n : ℕ) :
    (enrichedLeftKanFreeIso (coneCriticalEdgeIndex n) (op (SimplicialThickening.mk (⊥ : Vertex.{u} 1)))
      (max (coneWeight (⊥ : Vertex.{u} 1)).toSSet)).inv ≫
        ((EnrichedLeftKan.leftExtension (coneCriticalEdgeIndex n)).map coneSharpRootFreeLeg ≫
          coneCriticalConeSharpEdgeMap n) = coneCriticalEdgeConeSharpLeg n := by
  let C := (Index.{u} 1)ᵒᵖ
  let D := (Index.{u} (n + 2))ᵒᵖ
  let j := coneCriticalEdgeIndex.{u} n
  let c := op (SimplicialThickening.mk (⊥ : Vertex.{u} 1))
  let A := max (coneWeight (⊥ : Vertex.{u} 1)).toSSet
  apply (enrichedFreeHomEquiv D (j.obj c) A (coneCriticalDiagram n)).injective
  have hl := enrichedLeftKanFreeIso_inv_map_post j c A coneSharpRootFreeLeg (coneCriticalConeSharpEdgeMap n)
  have hm := congrArg (enrichedFreeHomEquiv C c A ((enrichedDiagramRestrict j).obj (coneCriticalDiagram n)))
    (congrArg (fun f => coneSharpRootFreeLeg ≫ f) (coneCriticalConeSharpEdgeMap_homEquiv n))
  have hr := enrichedFreeHomEquiv_post C c A coneSharpRootFreeLeg (coneCriticalEdgeSharpOperator n)
  change enrichedFreeHomEquiv C c A _ (coneSharpRootFreeLeg ≫ coneCriticalEdgeSharpOperator n) =
    (enrichedFreeUnit C c A ≫ coneSharpRootFreeLeg.app c) ≫ coneCriticalEdgeSharpRoot n at hr
  rw [coneSharpRootFreeLeg_unit] at hr
  exact hl.trans (hm.trans (hr.trans ((Category.id_comp (coneCriticalEdgeSharpRoot n)).trans
    (coneCriticalEdgeConeSharpLeg_unit n).symm)))

/-- The original minimal free-image unit and SAME full horn mate retain the actual predecessor horn leg. -/
theorem coneCriticalEdgeFreeImage_inv_hornMinimal (n : ℕ) :
    (enrichedLeftKanFreeIso (coneCriticalEdgeIndex n) (op (SimplicialThickening.mk (⊥ : Vertex.{u} 1)))
      (coneWeight (⊥ : Vertex.{u} 1))).inv ≫
        ((EnrichedLeftKan.leftExtension (coneCriticalEdgeIndex n)).map (coneRootFreeMap 1) ≫
          coneCriticalHornEdgeMap n) = coneCriticalEdgeHornMinimalLeg n := by
  let C := (Index.{u} 1)ᵒᵖ
  let D := (Index.{u} (n + 2))ᵒᵖ
  let j := coneCriticalEdgeIndex.{u} n
  let c := op (SimplicialThickening.mk (⊥ : Vertex.{u} 1))
  let A := coneWeight (⊥ : Vertex.{u} 1)
  let F := coneRootHornDiagram (Fin.last (n + 2))
  apply (enrichedFreeHomEquiv D (j.obj c) A F).injective
  have hl := enrichedLeftKanFreeIso_inv_map_post j c A (coneRootFreeMap 1) (coneCriticalHornEdgeMap n)
  have hm := congrArg (enrichedFreeHomEquiv C c A ((enrichedDiagramRestrict j).obj F))
    (congrArg (fun f => coneRootFreeMap 1 ≫ f) (coneCriticalHornEdgeMap_homEquiv n))
  have hr := enrichedFreeHomEquiv_post C c A (coneRootFreeMap 1) (coneCriticalEdgeMinimalHornOperator n)
  change enrichedFreeHomEquiv C c A _ (coneRootFreeMap 1 ≫ coneCriticalEdgeMinimalHornOperator n) =
    (enrichedFreeUnit C c A ≫ (coneRootFreeMap 1).app c) ≫ coneCriticalEdgeMinimalHornRoot n at hr
  rw [coneRootFreeMap_unit] at hr
  exact hl.trans (hm.trans (hr.trans ((Category.id_comp (coneCriticalEdgeMinimalHornRoot n)).trans
    (coneCriticalEdgeHornMinimalLeg_unit n).symm)))

/-- The SAME sharp free-image unit and full critically marked horn mate retain the whole original predecessor leg. -/
theorem coneCriticalEdgeFreeImage_inv_hornSharp (n : ℕ) :
    (enrichedLeftKanFreeIso (coneCriticalEdgeIndex n) (op (SimplicialThickening.mk (⊥ : Vertex.{u} 1)))
      (max (coneWeight (⊥ : Vertex.{u} 1)).toSSet)).inv ≫
        ((EnrichedLeftKan.leftExtension (coneCriticalEdgeIndex n)).map coneSharpRootFreeLeg ≫
          coneCriticalHornSharpEdgeMap n) = coneCriticalEdgeHornSharpLeg n := by
  let C := (Index.{u} 1)ᵒᵖ
  let D := (Index.{u} (n + 2))ᵒᵖ
  let j := coneCriticalEdgeIndex.{u} n
  let c := op (SimplicialThickening.mk (⊥ : Vertex.{u} 1))
  let A := max (coneWeight (⊥ : Vertex.{u} 1)).toSSet
  apply (enrichedFreeHomEquiv D (j.obj c) A (coneCriticalHornDiagram n)).injective
  have hl := enrichedLeftKanFreeIso_inv_map_post j c A coneSharpRootFreeLeg (coneCriticalHornSharpEdgeMap n)
  have hm := congrArg (enrichedFreeHomEquiv C c A ((enrichedDiagramRestrict j).obj (coneCriticalHornDiagram n)))
    (congrArg (fun f => coneSharpRootFreeLeg ≫ f) (coneCriticalHornSharpEdgeMap_homEquiv n))
  have hr := enrichedFreeHomEquiv_post C c A coneSharpRootFreeLeg (coneCriticalEdgeSharpHornOperator n)
  change enrichedFreeHomEquiv C c A _ (coneSharpRootFreeLeg ≫ coneCriticalEdgeSharpHornOperator n) =
    (enrichedFreeUnit C c A ≫ coneSharpRootFreeLeg.app c) ≫ coneCriticalEdgeSharpHornRoot n at hr
  rw [coneSharpRootFreeLeg_unit] at hr
  exact hl.trans (hm.trans (hr.trans ((Category.id_comp (coneCriticalEdgeSharpHornRoot n)).trans
    (coneCriticalEdgeHornSharpLeg_unit n).symm)))

/-- The original full critical cone marking square is a genuine pushout of the SAME whole original interval chart. -/
theorem coneCriticalWholeConeEdgeMarking_isPushout (n : ℕ) :
    IsPushout (coneCriticalEdgeMarkingChartMap n) (coneCriticalConeEdgeMap n)
      (coneCriticalConeSharpEdgeMap n) (coneCriticalDiagramMark.{u} n) := by
  let j := coneCriticalEdgeIndex.{u} n
  let L := EnrichedLeftKan.leftExtension j
  let c := op (SimplicialThickening.mk (⊥ : Vertex.{u} 1))
  let A := coneWeight (⊥ : Vertex.{u} 1)
  let M := max A.toSSet
  let eA := enrichedLeftKanFreeIso j c A
  let eM := enrichedLeftKanFreeIso j c M
  let _ : PreservesColimitsOfSize.{u, u} L := (EnrichedLeftKan.adjunction j).leftAdjoint_preservesColimits
  have ht := (IsPushout.of_isColimit coneSharpRootMarkEnrichedIsColimit.{u}).map L
  have hc := IsPushout.of_isColimit (coneCriticalEdgeConeEnrichedIsColimit.{u} n)
  have hb : IsPushout (L.map coneSharpRootMarkFreeMap)
      (L.map (coneRootFreeMap 1) ≫ coneCriticalConeEdgeMap n)
      (L.map coneSharpRootFreeLeg ≫ coneCriticalConeSharpEdgeMap n) (coneCriticalDiagramMark n) := by
    apply hc.of_iso eA.symm eM.symm (Iso.refl _) (Iso.refl _)
    · exact (coneCriticalEdgeFreeImage_inv_marking n).symm
    · exact (Category.comp_id _).trans (coneCriticalEdgeFreeImage_inv_coneMinimal n).symm
    · exact (Category.comp_id _).trans (coneCriticalEdgeFreeImage_inv_coneSharp n).symm
    · exact (Category.comp_id _).trans (Category.id_comp _).symm
  exact hb.of_top (coneCriticalConeEdgeMarking_condition n) ht

/-- The SAME entire original terminal horn marking square is the genuine full original interval chart pushout. -/
theorem coneCriticalWholeHornEdgeMarking_isPushout (n : ℕ) :
    IsPushout (coneCriticalEdgeMarkingChartMap n) (coneCriticalHornEdgeMap n)
      (coneCriticalHornSharpEdgeMap n) (coneCriticalHornDiagramMark.{u} n) := by
  let j := coneCriticalEdgeIndex.{u} n
  let L := EnrichedLeftKan.leftExtension j
  let c := op (SimplicialThickening.mk (⊥ : Vertex.{u} 1))
  let A := coneWeight (⊥ : Vertex.{u} 1)
  let M := max A.toSSet
  let eA := enrichedLeftKanFreeIso j c A
  let eM := enrichedLeftKanFreeIso j c M
  let _ : PreservesColimitsOfSize.{u, u} L := (EnrichedLeftKan.adjunction j).leftAdjoint_preservesColimits
  have ht := (IsPushout.of_isColimit coneSharpRootMarkEnrichedIsColimit.{u}).map L
  have hc := IsPushout.of_isColimit (coneCriticalEdgeHornEnrichedIsColimit.{u} n)
  have hb : IsPushout (L.map coneSharpRootMarkFreeMap)
      (L.map (coneRootFreeMap 1) ≫ coneCriticalHornEdgeMap n)
      (L.map coneSharpRootFreeLeg ≫ coneCriticalHornSharpEdgeMap n) (coneCriticalHornDiagramMark n) := by
    apply hc.of_iso eA.symm eM.symm (Iso.refl _) (Iso.refl _)
    · exact (coneCriticalEdgeFreeImage_inv_marking n).symm
    · exact (Category.comp_id _).trans (coneCriticalEdgeFreeImage_inv_hornMinimal n).symm
    · exact (Category.comp_id _).trans (coneCriticalEdgeFreeImage_inv_hornSharp n).symm
    · exact (Category.comp_id _).trans (Category.id_comp _).symm
  exact hb.of_top (coneCriticalHornEdgeMarking_condition n) ht

/-- The whole original critical cone retains its exact full interval marking cocone. -/
def coneCriticalWholeConeEdgeMarkingCocone (n : ℕ) :
    PushoutCocone (coneCriticalEdgeMarkingChartMap n) (coneCriticalConeEdgeMap n) :=
  PushoutCocone.mk (coneCriticalConeSharpEdgeMap n) (coneCriticalDiagramMark n)
    (coneCriticalConeEdgeMarking_condition n)

/-- The SAME whole cone cocone is an actual marked enriched colimit over the full interval chart. -/
def coneCriticalWholeConeEdgeMarkingIsColimit (n : ℕ) :
    IsColimit (coneCriticalWholeConeEdgeMarkingCocone.{u} n) :=
  (coneCriticalWholeConeEdgeMarking_isPushout n).isColimit

/-- The entire original terminal horn keeps the SAME full original interval marking cocone. -/
def coneCriticalWholeHornEdgeMarkingCocone (n : ℕ) :
    PushoutCocone (coneCriticalEdgeMarkingChartMap n) (coneCriticalHornEdgeMap n) :=
  PushoutCocone.mk (coneCriticalHornSharpEdgeMap n) (coneCriticalHornDiagramMark n)
    (coneCriticalHornEdgeMarking_condition n)

/-- The SAME complete original horn cocone is its genuine full marked enriched colimit. -/
def coneCriticalWholeHornEdgeMarkingIsColimit (n : ℕ) :
    IsColimit (coneCriticalWholeHornEdgeMarkingCocone.{u} n) :=
  (coneCriticalWholeHornEdgeMarking_isPushout n).isColimit

end SSet.Marked.CoherentWeight
