/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Universality.RSWContactFreeSourceArc
import Code.Universality.RSWAxisOrContactObstruction
























open Function MeasureTheory Set

namespace StatMech
namespace Universality

open StatMech.Percolation
open StatMech.Lattice
open StatMech.RSW.Box




theorem rlc_mem_axisGapEdges_iff_edgeBoxIncidentGap
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper) (e : Sym2 (Site 2)) :
    e ∈ rlc_axisGapEdges G ↔ rlc_edgeBoxIncidentGap G e := by
  induction e using Sym2.inductionOn with
  | _ v w =>
      constructor
      · intro he
        have hbox := rlc_axisGapEdges_endpoints_mem_box G hn hlt he
        refine ⟨?_, ?_⟩
        · intro z hz
          rw [Sym2.mem_iff] at hz
          rcases hz with rfl | rfl
          · exact hbox.1
          · exact hbox.2
        · rw [rlc_axisGapEdges, Finset.mem_union] at he
          rcases he with he | he
          · exact (Finset.mem_filter.mp he).2
          · have heq : s(v, w) = s(G.lowerVertex, G.seedVertex) := by
              simpa [RlcAxisBarrierGap.firstEdge] using he
            refine ⟨G.seedVertex, G.seedVertex_mem_region_of_lt hn hlt, ?_⟩
            rw [heq, Sym2.mem_iff]
            simp
      · exact rlc_mem_axisGapEdges_of_edgeBoxIncidentGap G



theorem rlc_mixedWired_faceBoundary_sourceSupported_iff_sourceLocal
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2))) {f g : Site 2}
    (hfg : (faceBoundaryGraph
      (rlc_mixedWiredReachSet G omega)).Adj f g) :
    sharedPrimalEdge f g ∈ rlc_mixedAxisGapEdges G ↔
      rlc_boundarySourceLocallySupported G (sharedPrimalEdge f g) := by
  have hpims : rlc_pimsEdgeEquiv
      s(rlc_dualReflect f, rlc_dualReflect g) = sharedPrimalEdge f g :=
    rlc_pimsEdgeEquiv_reflected_faceBoundaryEdge
      (rlc_mixedWiredReachSet G omega) hfg
  calc
    sharedPrimalEdge f g ∈ rlc_mixedAxisGapEdges G ↔
        rlc_pimsEdgeEquiv s(rlc_dualReflect f, rlc_dualReflect g) ∈
          rlc_mixedAxisGapEdges G := by rw [hpims]
    _ ↔ sharedPrimalEdge f g ∈ rlc_axisGapEdges G ∨
          sharedPrimalEdge f g ∈ rlc_reflectedPathEdges gamma.1 ∨
          sharedPrimalEdge f g ∈ rlc_reflectedPathEdges gamma'.1 :=
      rlc_mixedWired_faceBoundary_preimage_mem_mixedAxisGapEdges_iff
        G hn hlt omega hfg
    _ ↔ rlc_boundarySourceLocallySupported G
          (sharedPrimalEdge f g) := by
      unfold rlc_boundarySourceLocallySupported
      rw [← rlc_mem_axisGapEdges_iff_edgeBoxIncidentGap G hn hlt]


theorem rlc_faceBoundaryWalk_sourceSupported_iff_sourceLocal
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2))) {x y : Site 2}
    (c : (faceBoundaryGraph
      (rlc_mixedWiredReachSet G omega)).Walk x y) :
    RlcFaceBoundaryWalkSourceSupported G omega c ↔
      ∀ {f g : Site 2}, s(f, g) ∈ c.edges →
        rlc_boundarySourceLocallySupported G (sharedPrimalEdge f g) := by
  constructor
  · intro hsource f g hfg
    exact (rlc_mixedWired_faceBoundary_sourceSupported_iff_sourceLocal
      G hn hlt omega (c.adj_of_mem_edges hfg)).mp (hsource hfg)
  · intro hlocal f g hfg
    exact (rlc_mixedWired_faceBoundary_sourceSupported_iff_sourceLocal
      G hn hlt omega (c.adj_of_mem_edges hfg)).mpr (hlocal hfg)



theorem rlc_contourEdgeRelaxedLocal_iff_targetLocal_of_sourceSupported
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2))) {f g : Site 2}
    (hfg : (faceBoundaryGraph
      (rlc_mixedWiredReachSet G omega)).Adj f g)
    (hsource : sharedPrimalEdge f g ∈ rlc_mixedAxisGapEdges G) :
    rlc_contourEdgeRelaxedLocal G f g ↔
      rlc_reflectedTargetLocallySupported G
        s(rlc_dualReflect f, rlc_dualReflect g) := by
  have hsourceLocal :=
    (rlc_mixedWired_faceBoundary_sourceSupported_iff_sourceLocal
      G hn hlt omega hfg).mp hsource
  constructor
  · rintro (hexposed | ⟨htarget, _hsource⟩)
    · exact Or.inl hexposed
    · exact htarget
  · intro htarget
    exact Or.inr ⟨htarget, hsourceLocal⟩



theorem rlc_contourEdgeRelaxedLocal_comm_of_adj
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') {f g : Site 2}
    (hfg : (hypercubicLattice 2).Adj f g) :
    rlc_contourEdgeRelaxedLocal G f g ↔
      rlc_contourEdgeRelaxedLocal G g f := by
  unfold rlc_contourEdgeRelaxedLocal
  rw [show s(rlc_dualReflect g, rlc_dualReflect f) =
      s(rlc_dualReflect f, rlc_dualReflect g) from Sym2.eq_swap]
  rw [sharedPrimalEdge_comm_of_adj hfg]



theorem rlc_contourEdgeRelaxedLocal_of_mk_eq
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    {f g a b : Site 2} (hab : (hypercubicLattice 2).Adj a b)
    (he : s(f, g) = s(a, b))
    (hlocal : rlc_contourEdgeRelaxedLocal G a b) :
    rlc_contourEdgeRelaxedLocal G f g := by
  rw [Sym2.eq_iff] at he
  rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hlocal
  · exact (rlc_contourEdgeRelaxedLocal_comm_of_adj G hab).mp hlocal



theorem rlc_faceBoundaryWalk_relaxedLocal_iff_targetLocal_of_sourceSupported
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2))) {x y : Site 2}
    (c : (faceBoundaryGraph
      (rlc_mixedWiredReachSet G omega)).Walk x y)
    (hsource : RlcFaceBoundaryWalkSourceSupported G omega c) :
    (∀ {f g : Site 2}, s(f, g) ∈ c.edges →
        rlc_contourEdgeRelaxedLocal G f g) ↔
      ∀ {f g : Site 2}, s(f, g) ∈ c.edges →
        rlc_reflectedTargetLocallySupported G
          s(rlc_dualReflect f, rlc_dualReflect g) := by
  constructor <;> intro h f g hfg
  · exact (rlc_contourEdgeRelaxedLocal_iff_targetLocal_of_sourceSupported
      G hn hlt omega (c.adj_of_mem_edges hfg) (hsource hfg)).mp (h hfg)
  · exact (rlc_contourEdgeRelaxedLocal_iff_targetLocal_of_sourceSupported
      G hn hlt omega (c.adj_of_mem_edges hfg) (hsource hfg)).mpr (h hfg)




theorem rlc_mixedWiredConnectorEvent_dualReflect_of_relaxedLocalWalk_meets_paths
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2))) {u v : Site 2}
    (c : (faceBoundaryGraph
      (rlc_mixedWiredReachSet G omega)).Walk u v)
    (hlocal : ∀ {f g : Site 2}, s(f, g) ∈ c.edges →
      rlc_contourEdgeRelaxedLocal G f g)
    (hright : ∃ x ∈ c.support,
      rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
    (hleft : ∃ y ∈ c.support,
      rlc_dualReflect y ∈ rlc_pathVertices gamma'.1) :
    rlc_dualReflectConfig omega ∈ rlc_mixedWiredConnectorEvent G := by
  obtain ⟨x, hx, hxPath⟩ := hright
  obtain ⟨y, hy, hyPath⟩ := hleft
  let a : (faceBoundaryGraph
      (rlc_mixedWiredReachSet G omega)).Walk x y :=
    (c.takeUntil x hx).reverse.append (c.takeUntil y hy)
  have haLocal : ∀ {f g : Site 2}, s(f, g) ∈ a.edges →
      rlc_contourEdgeRelaxedLocal G f g := by
    intro f g hfg
    dsimp only [a] at hfg
    rw [SimpleGraph.Walk.edges_append,
      SimpleGraph.Walk.edges_reverse, List.mem_append,
      List.mem_reverse] at hfg
    rcases hfg with hfg | hfg
    · exact hlocal (c.edges_takeUntil_subset hx hfg)
    · exact hlocal (c.edges_takeUntil_subset hy hfg)
  exact rlc_mixedWiredConnectorEvent_dualReflect_of_relaxedLocalArc
    G hn hlt omega a hxPath hyPath haLocal



theorem rlc_mixedWiredConnectorEvent_dualReflect_of_sourceSupportedWalk_meets_paths
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2))) {u v : Site 2}
    (c : (faceBoundaryGraph
      (rlc_mixedWiredReachSet G omega)).Walk u v)
    (hsource : RlcFaceBoundaryWalkSourceSupported G omega c)
    (htarget : ∀ {f g : Site 2}, s(f, g) ∈ c.edges →
      rlc_reflectedTargetLocallySupported G
        s(rlc_dualReflect f, rlc_dualReflect g))
    (hright : ∃ x ∈ c.support,
      rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
    (hleft : ∃ y ∈ c.support,
      rlc_dualReflect y ∈ rlc_pathVertices gamma'.1) :
    rlc_dualReflectConfig omega ∈ rlc_mixedWiredConnectorEvent G := by
  apply rlc_mixedWiredConnectorEvent_dualReflect_of_relaxedLocalWalk_meets_paths
    G hn hlt omega c
  · exact (rlc_faceBoundaryWalk_relaxedLocal_iff_targetLocal_of_sourceSupported
      G hn hlt omega c hsource).mpr htarget
  · exact hright
  · exact hleft




theorem rlc_sourceSupportedWalk_targetDefect_of_dualReflect_failure
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hno : rlc_dualReflectConfig omega ∉ rlc_mixedWiredConnectorEvent G)
    {u v : Site 2}
    (c : (faceBoundaryGraph
      (rlc_mixedWiredReachSet G omega)).Walk u v)
    (hsource : RlcFaceBoundaryWalkSourceSupported G omega c)
    (hright : ∃ x ∈ c.support,
      rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
    (hleft : ∃ y ∈ c.support,
      rlc_dualReflect y ∈ rlc_pathVertices gamma'.1) :
    ∃ f g : Site 2, s(f, g) ∈ c.edges ∧
      ¬ rlc_reflectedTargetLocallySupported G
        s(rlc_dualReflect f, rlc_dualReflect g) := by
  by_contra hdefect
  have htarget : ∀ {f g : Site 2}, s(f, g) ∈ c.edges →
      rlc_reflectedTargetLocallySupported G
        s(rlc_dualReflect f, rlc_dualReflect g) := by
    intro f g hfg
    by_contra hbad
    exact hdefect ⟨f, g, hfg, hbad⟩
  exact hno
    (rlc_mixedWiredConnectorEvent_dualReflect_of_sourceSupportedWalk_meets_paths
      G hn hlt omega c hsource htarget hright hleft)






def RlcRelaxedLocalDefectsSeparateTraces {n : ℤ}
    {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (omega : ConfigSpace (Sym2 (Site 2))) : Prop :=
  ∀ {x y : Site 2}
    (a : (faceBoundaryGraph
      (rlc_mixedWiredReachSet G omega)).Walk x y),
    rlc_dualReflect x ∈ rlc_pathVertices gamma.1 →
    rlc_dualReflect y ∈ rlc_pathVertices gamma'.1 →
    ∃ f g : Site 2, s(f, g) ∈ a.edges ∧
      ¬ rlc_contourEdgeRelaxedLocal G f g



def RlcRelaxedLocalTraceArcExists {n : ℤ}
    {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (omega : ConfigSpace (Sym2 (Site 2))) : Prop :=
  ∃ (x y : Site 2)
    (a : (faceBoundaryGraph
      (rlc_mixedWiredReachSet G omega)).Walk x y),
    rlc_dualReflect x ∈ rlc_pathVertices gamma.1 ∧
      rlc_dualReflect y ∈ rlc_pathVertices gamma'.1 ∧
      ∀ {f g : Site 2}, s(f, g) ∈ a.edges →
        rlc_contourEdgeRelaxedLocal G f g




theorem rlc_relaxedLocalTraceArcExists_iff_not_defectCut
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (omega : ConfigSpace (Sym2 (Site 2))) :
    RlcRelaxedLocalTraceArcExists G omega ↔
      ¬ RlcRelaxedLocalDefectsSeparateTraces G omega := by
  constructor
  · rintro ⟨x, y, a, hxPath, hyPath, hlocal⟩ hcut
    obtain ⟨f, g, hfg, hbad⟩ := hcut a hxPath hyPath
    exact hbad (hlocal hfg)
  · intro hcut
    unfold RlcRelaxedLocalDefectsSeparateTraces at hcut
    push Not at hcut
    obtain ⟨x, y, a, hxPath, hyPath, hlocal⟩ := hcut
    exact ⟨x, y, a, hxPath, hyPath,
      fun {_ _} hfg => hlocal _ _ hfg⟩


theorem rlc_mixedWiredConnectorEvent_dualReflect_of_relaxedLocalTraceArc
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2)))
    (h : RlcRelaxedLocalTraceArcExists G omega) :
    rlc_dualReflectConfig omega ∈ rlc_mixedWiredConnectorEvent G := by
  obtain ⟨x, y, a, hxPath, hyPath, hlocal⟩ := h
  exact rlc_mixedWiredConnectorEvent_dualReflect_of_relaxedLocalArc
    G hn hlt omega a hxPath hyPath hlocal


theorem rlc_relaxedLocalDefectsSeparateTraces_of_dualReflect_failure
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hno : rlc_dualReflectConfig omega ∉
      rlc_mixedWiredConnectorEvent G) :
    RlcRelaxedLocalDefectsSeparateTraces G omega := by
  intro x y a hxPath hyPath
  by_contra hdefect
  have hlocal : ∀ {f g : Site 2}, s(f, g) ∈ a.edges →
      rlc_contourEdgeRelaxedLocal G f g := by
    intro f g hfg
    by_contra hbad
    exact hdefect ⟨f, g, hfg, hbad⟩
  exact hno
    (rlc_mixedWiredConnectorEvent_dualReflect_of_relaxedLocalArc
      G hn hlt omega a hxPath hyPath hlocal)




theorem rlc_mixedWiredConnectorEvent_dualReflect_of_not_defectCut
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hcut : ¬ RlcRelaxedLocalDefectsSeparateTraces G omega) :
    rlc_dualReflectConfig omega ∈ rlc_mixedWiredConnectorEvent G := by
  unfold RlcRelaxedLocalDefectsSeparateTraces at hcut
  push Not at hcut
  obtain ⟨x, y, a, hxPath, hyPath, hlocal⟩ := hcut
  exact rlc_mixedWiredConnectorEvent_dualReflect_of_relaxedLocalArc
    G hn hlt omega a hxPath hyPath
      (fun {_ _} hfg => hlocal _ _ hfg)




def RlcRelaxedLocalDefectsHitTraceSubwalksOf {n : ℤ}
    {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (omega : ConfigSpace (Sym2 (Site 2))) {u v : Site 2}
    (p : (faceBoundaryGraph
      (rlc_mixedWiredReachSet G omega)).Walk u v) : Prop :=
  ∀ {x y : Site 2}
    (a : (faceBoundaryGraph
      (rlc_mixedWiredReachSet G omega)).Walk x y),
    (∀ e ∈ a.edges, e ∈ p.edges) →
    rlc_dualReflect x ∈ rlc_pathVertices gamma.1 →
    rlc_dualReflect y ∈ rlc_pathVertices gamma'.1 →
    ∃ f g : Site 2, s(f, g) ∈ a.edges ∧
      ¬ rlc_contourEdgeRelaxedLocal G f g




def RlcFaceBoundaryWalkCarriesRelaxedTraceArc {n : ℤ}
    {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (omega : ConfigSpace (Sym2 (Site 2))) {u v : Site 2}
    (p : (faceBoundaryGraph
      (rlc_mixedWiredReachSet G omega)).Walk u v) : Prop :=
  ∃ (x y : Site 2)
    (a : (faceBoundaryGraph
      (rlc_mixedWiredReachSet G omega)).Walk x y),
    (∀ e ∈ a.edges, e ∈ p.edges) ∧
      rlc_dualReflect x ∈ rlc_pathVertices gamma.1 ∧
      rlc_dualReflect y ∈ rlc_pathVertices gamma'.1 ∧
      ∀ {f g : Site 2}, s(f, g) ∈ a.edges →
        rlc_contourEdgeRelaxedLocal G f g



theorem rlc_carriesRelaxedTraceArc_iff_not_defectsHitTraceSubwalksOf
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (omega : ConfigSpace (Sym2 (Site 2))) {u v : Site 2}
    (p : (faceBoundaryGraph
      (rlc_mixedWiredReachSet G omega)).Walk u v) :
    RlcFaceBoundaryWalkCarriesRelaxedTraceArc G omega p ↔
      ¬ RlcRelaxedLocalDefectsHitTraceSubwalksOf G omega p := by
  classical
  constructor
  · rintro ⟨x, y, a, hsub, hx, hy, hlocal⟩ hhit
    obtain ⟨f, g, hfg, hbad⟩ := hhit a hsub hx hy
    exact hbad (hlocal hfg)
  · intro hnot
    unfold RlcRelaxedLocalDefectsHitTraceSubwalksOf at hnot
    push Not at hnot
    obtain ⟨x, y, a, hsub, hx, hy, hlocal⟩ := hnot
    exact ⟨x, y, a, hsub, hx, hy,
      fun {_ _} hfg => hlocal _ _ hfg⟩



theorem rlc_mixedWiredConnectorEvent_dualReflect_of_carriesRelaxedTraceArc
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2))) {u v : Site 2}
    (p : (faceBoundaryGraph
      (rlc_mixedWiredReachSet G omega)).Walk u v)
    (hcarry : RlcFaceBoundaryWalkCarriesRelaxedTraceArc G omega p) :
    rlc_dualReflectConfig omega ∈ rlc_mixedWiredConnectorEvent G := by
  obtain ⟨x, y, a, _hsub, hx, hy, hlocal⟩ := hcarry
  exact rlc_mixedWiredConnectorEvent_dualReflect_of_relaxedLocalArc
    G hn hlt omega a hx hy hlocal


theorem RlcRelaxedLocalDefectsSeparateTraces.hitTraceSubwalksOf
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {G : RlcAxisBarrierGap gamma gamma'}
    {omega : ConfigSpace (Sym2 (Site 2))}
    (hcut : RlcRelaxedLocalDefectsSeparateTraces G omega)
    {u v : Site 2}
    (p : (faceBoundaryGraph
      (rlc_mixedWiredReachSet G omega)).Walk u v) :
    RlcRelaxedLocalDefectsHitTraceSubwalksOf G omega p := by
  intro x y a _hsub hxPath hyPath
  exact hcut a hxPath hyPath





def RlcFailureComplementaryArcEscapesDefectCut {n : ℤ}
    {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (omega : ConfigSpace (Sym2 (Site 2))) : Prop :=
  ∃ (t : ℤ) (f g : Site 2)
    (p : (faceBoundaryGraph
      (rlc_mixedWiredReachSet G omega)).Walk f g),
    G.lower ≤ t ∧ t < G.upper ∧
      ![0, t] ∈ rlc_mixedWiredReachSet G omega ∧
      ![0, t + 1] ∉ rlc_mixedWiredReachSet G omega ∧
      (faceBoundaryGraph
        (rlc_mixedWiredReachSet G omega)).Adj f g ∧
      sharedPrimalEdge f g = s(![0, t], ![0, t + 1]) ∧
      s(f, g) ∉ p.edges ∧
      RlcFaceBoundaryWalkCarriesRelaxedTraceArc G omega p



theorem rlc_mixedWiredConnectorEvent_dualReflect_of_failureComplementaryArcEscapes
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hplace : RlcFailureComplementaryArcEscapesDefectCut G omega) :
    rlc_dualReflectConfig omega ∈ rlc_mixedWiredConnectorEvent G := by
  obtain ⟨_t, _f, _g, p, _htLower, _htUpper, _htIn, _htOut,
      _hfg, _hshared, _hanchor, hcarry⟩ := hplace
  exact rlc_mixedWiredConnectorEvent_dualReflect_of_carriesRelaxedTraceArc
    G hn hlt omega p hcarry




theorem not_failureComplementaryArcEscapes_of_dualReflect_failure
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hno : rlc_dualReflectConfig omega ∉
      rlc_mixedWiredConnectorEvent G) :
    ¬ RlcFailureComplementaryArcEscapesDefectCut G omega := by
  intro hplace
  exact hno
    (rlc_mixedWiredConnectorEvent_dualReflect_of_failureComplementaryArcEscapes
      G hn hlt omega hplace)




theorem rlc_doubleFailure_complementaryArc_trace_or_relaxedLocalDefect
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hno : omega ∉ rlc_mixedWiredConnectorEvent G)
    (hnoReflect :
      rlc_dualReflectConfig omega ∉ rlc_mixedWiredConnectorEvent G) :
    ∃ (t : ℤ) (f g : Site 2)
      (p : (faceBoundaryGraph
        (rlc_mixedWiredReachSet G omega)).Walk f g),
      G.lower ≤ t ∧ t < G.upper ∧
      ![0, t] ∈ rlc_mixedWiredReachSet G omega ∧
      ![0, t + 1] ∉ rlc_mixedWiredReachSet G omega ∧
      (faceBoundaryGraph
        (rlc_mixedWiredReachSet G omega)).Adj f g ∧
      sharedPrimalEdge f g = s(![0, t], ![0, t + 1]) ∧
      s(f, g) ∉ p.edges ∧
      ((∀ x ∈ p.support,
          rlc_dualReflect x ∉ rlc_pathVertices gamma.1) ∨
        (∀ y ∈ p.support,
          rlc_dualReflect y ∉ rlc_pathVertices gamma'.1) ∨
        ∃ a b : Site 2, s(a, b) ∈ p.edges ∧
          ¬ rlc_contourEdgeRelaxedLocal G a b) := by
  classical
  obtain ⟨t, f, g, htLower, htUpper, htIn, htOut,
      hfg, hshared, p, hanchor⟩ :=
    rlc_mixedWiredReachSet_faceBoundaryComplementaryArc_with_anchorAdj
      G omega hno
  refine ⟨t, f, g, p, htLower, htUpper, htIn, htOut,
    hfg, hshared, hanchor, ?_⟩
  by_cases hright : ∃ x ∈ p.support,
      rlc_dualReflect x ∈ rlc_pathVertices gamma.1
  · by_cases hleft : ∃ y ∈ p.support,
        rlc_dualReflect y ∈ rlc_pathVertices gamma'.1
    · right
      right
      by_contra hdefect
      have hlocal : ∀ {a b : Site 2}, s(a, b) ∈ p.edges →
          rlc_contourEdgeRelaxedLocal G a b := by
        intro a b hab
        by_contra hbad
        exact hdefect ⟨a, b, hab, hbad⟩
      exact hnoReflect
        (rlc_mixedWiredConnectorEvent_dualReflect_of_relaxedLocalWalk_meets_paths
          G hn hlt omega p hlocal hright hleft)
    · right
      left
      intro y hy hyPath
      exact hleft ⟨y, hy, hyPath⟩
  · left
    intro x hx hxPath
    exact hright ⟨x, hx, hxPath⟩





theorem rlc_doubleFailure_complementaryArc_defectCut
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hno : omega ∉ rlc_mixedWiredConnectorEvent G)
    (hnoReflect :
      rlc_dualReflectConfig omega ∉ rlc_mixedWiredConnectorEvent G) :
    ∃ (t : ℤ) (f g : Site 2)
      (p : (faceBoundaryGraph
        (rlc_mixedWiredReachSet G omega)).Walk f g),
      G.lower ≤ t ∧ t < G.upper ∧
      ![0, t] ∈ rlc_mixedWiredReachSet G omega ∧
      ![0, t + 1] ∉ rlc_mixedWiredReachSet G omega ∧
      (faceBoundaryGraph
        (rlc_mixedWiredReachSet G omega)).Adj f g ∧
      sharedPrimalEdge f g = s(![0, t], ![0, t + 1]) ∧
      s(f, g) ∉ p.edges ∧
      RlcRelaxedLocalDefectsHitTraceSubwalksOf G omega p := by
  obtain ⟨t, f, g, htLower, htUpper, htIn, htOut,
      hfg, hshared, p, hanchor⟩ :=
    rlc_mixedWiredReachSet_faceBoundaryComplementaryArc_with_anchorAdj
      G omega hno
  refine ⟨t, f, g, p, htLower, htUpper, htIn, htOut,
    hfg, hshared, hanchor, ?_⟩
  exact RlcRelaxedLocalDefectsSeparateTraces.hitTraceSubwalksOf
    (rlc_relaxedLocalDefectsSeparateTraces_of_dualReflect_failure
      G hn hlt omega hnoReflect) p



private theorem rlc_traceSplitCounterexample_boundary_adj₀₁
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hK : rlc_mixedWiredReachSet rlc_windingSideCounterexampleGap omega =
      (rlc_pathVertices rlc_traceSplitCounterexampleRight.1 : Set (Site 2))) :
    (faceBoundaryGraph
      (rlc_mixedWiredReachSet rlc_windingSideCounterexampleGap omega)).Adj
        ![-1, -2] ![-1, -1] := by
  apply (faceBoundaryGraph_adj_vert
    (rlc_mixedWiredReachSet rlc_windingSideCounterexampleGap omega)
      (-1) (-1) ?_).symm
  rw [hK, rlc_traceSplitCounterexample_right_vertices]
  simp

private theorem rlc_traceSplitCounterexample_boundary_adj₁₂
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hK : rlc_mixedWiredReachSet rlc_windingSideCounterexampleGap omega =
      (rlc_pathVertices rlc_traceSplitCounterexampleRight.1 : Set (Site 2))) :
    (faceBoundaryGraph
      (rlc_mixedWiredReachSet rlc_windingSideCounterexampleGap omega)).Adj
        ![-1, -1] ![0, -1] := by
  apply (faceBoundaryGraph_adj_horiz
    (rlc_mixedWiredReachSet rlc_windingSideCounterexampleGap omega)
      0 (-1) ?_).symm
  rw [hK, rlc_traceSplitCounterexample_right_vertices]
  simp

private theorem rlc_traceSplitCounterexample_boundary_adj₂₃
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hK : rlc_mixedWiredReachSet rlc_windingSideCounterexampleGap omega =
      (rlc_pathVertices rlc_traceSplitCounterexampleRight.1 : Set (Site 2))) :
    (faceBoundaryGraph
      (rlc_mixedWiredReachSet rlc_windingSideCounterexampleGap omega)).Adj
        ![0, -1] ![1, -1] := by
  apply (faceBoundaryGraph_adj_horiz
    (rlc_mixedWiredReachSet rlc_windingSideCounterexampleGap omega)
      1 (-1) ?_).symm
  rw [hK, rlc_traceSplitCounterexample_right_vertices]
  simp



def rlc_traceSplitCounterexample_boundaryArc
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hK : rlc_mixedWiredReachSet rlc_windingSideCounterexampleGap omega =
      (rlc_pathVertices rlc_traceSplitCounterexampleRight.1 : Set (Site 2))) :
    (faceBoundaryGraph
      (rlc_mixedWiredReachSet rlc_windingSideCounterexampleGap omega)).Walk
        ![-1, -2] ![1, -1] :=
  .cons (rlc_traceSplitCounterexample_boundary_adj₀₁ omega hK)
    (.cons (rlc_traceSplitCounterexample_boundary_adj₁₂ omega hK)
      (.cons (rlc_traceSplitCounterexample_boundary_adj₂₃ omega hK) .nil))

@[simp] theorem rlc_traceSplitCounterexample_boundaryArc_edges
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hK : rlc_mixedWiredReachSet rlc_windingSideCounterexampleGap omega =
      (rlc_pathVertices rlc_traceSplitCounterexampleRight.1 : Set (Site 2))) :
    (rlc_traceSplitCounterexample_boundaryArc omega hK).edges =
      [s((![-1, -2] : Site 2), ![-1, -1]),
        s((![-1, -1] : Site 2), ![0, -1]),
        s((![0, -1] : Site 2), ![1, -1])] := by
  rfl

theorem rlc_traceSplitCounterexample_boundaryArc_rightContact :
    rlc_dualReflect (![-1, -2] : Site 2) ∈
      rlc_pathVertices rlc_traceSplitCounterexampleRight.1 := by
  rw [rlc_traceSplitCounterexample_right_vertices]
  simp [rlc_dualReflect, rlc_dualReflectFun]

theorem rlc_traceSplitCounterexample_boundaryArc_leftContact :
    rlc_dualReflect (![1, -1] : Site 2) ∈
      rlc_pathVertices rlc_traceSplitCounterexampleLeft.1 := by
  rw [rlc_traceSplitCounterexample_left_vertices]
  simp [rlc_dualReflect, rlc_dualReflectFun]

private theorem rlc_traceSplitCounterexample_one_zero_mem_axisGapRegion :
    (![1, 0] : Site 2) ∈
      rlc_axisGapRegion rlc_windingSideCounterexampleGap := by
  let G := rlc_windingSideCounterexampleGap
  let A := rlc_connectorAllowed rlc_traceSplitCounterexampleRight
    rlc_traceSplitCounterexampleLeft
  have hseed : G.seedVertex ∈ A :=
    G.seedVertex_mem_allowed_of_lt (by norm_num) (by
      change (-1 : ℤ) + 1 < 1
      omega)
  have hz : (![1, 0] : Site 2) ∈ A := by
    rw [show A = rlc_connectorAllowed rlc_traceSplitCounterexampleRight
      rlc_traceSplitCounterexampleLeft by rfl]
    rw [rlc_connectorAllowed, Finset.mem_sdiff]
    constructor
    · simp [rlc_connectorBox, mem_rect]
    · rw [rlc_connectorBarrier,
        rlc_traceSplitCounterexample_right_vertices,
        rlc_traceSplitCounterexample_left_vertices]
      simp [rlc_flipX, rlc_flipXFun]
  have hadj :
      ((hypercubicLattice 2).induce (A : Set (Site 2))).Adj
        ⟨G.seedVertex, by simpa using hseed⟩
        ⟨![1, 0], by simpa using hz⟩ := by
    change (hypercubicLattice 2).Adj G.seedVertex (![1, 0] : Site 2)
    simp [G, RlcAxisBarrierGap.seedVertex,
      rlc_windingSideCounterexampleGap, hypercubicLattice_adj,
      Fin.sum_univ_two]
  have hzSet : (![1, 0] : Site 2) ∈ rlc_axisGapRegionSet G :=
    ⟨hz, hseed, hadj.reachable⟩
  simpa [G, rlc_axisGapRegion] using hzSet

private theorem rlc_traceSplitCounterexample_right_first_edge :
    s((![0, -1] : Site 2), ![1, -1]) ∈
      rlc_pathEdges rlc_traceSplitCounterexampleRight.1 := by
  let W := rlc_ambientCrossingWalk rlc_traceSplitCounterexampleRight.1
  have hstart : (rlc_traceSplitCounterexampleRight.1.1 : Site 2) =
      ![0, -1] := by
    have hmem : (rlc_traceSplitCounterexampleRight.1.1 : Site 2) ∈
        rlc_pathVertices rlc_traceSplitCounterexampleRight.1 :=
      (rlc_mem_ambientCrossingWalk_support_iff_pathVertices
        rlc_traceSplitCounterexampleRight.1 _).mp
          (rlc_ambientCrossingWalk
            rlc_traceSplitCounterexampleRight.1).start_mem_support
    have hx : (rlc_traceSplitCounterexampleRight.1.1 : Site 2) 0 = 0 := by
      have hside := rlc_traceSplitCounterexampleRight.1.1.2
      rw [mem_leftSide] at hside
      exact hside.2
    rw [rlc_traceSplitCounterexample_right_vertices] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with hmem | hmem | hmem | hmem
    · exact hmem
    · rw [hmem] at hx
      simp at hx
    · rw [hmem] at hx
      simp at hx
    · rw [hmem] at hx
      simp at hx
  have hnil : ¬ W.Nil := by
    apply SimpleGraph.Walk.not_nil_of_ne
    intro heq
    have hxStart : (rlc_traceSplitCounterexampleRight.1.1 : Site 2) 0 = 0 := by
      have hside := rlc_traceSplitCounterexampleRight.1.1.2
      rw [mem_leftSide] at hside
      exact hside.2
    have hxEnd : (rlc_traceSplitCounterexampleRight.1.2.1 : Site 2) 0 = 2 := by
      have hside := rlc_traceSplitCounterexampleRight.1.2.1.2
      rw [mem_rightSide] at hside
      simpa using hside.2
    have hxEq := congrArg (fun z : Site 2 => z 0) heq
    have : (0 : ℤ) = 2 := hxStart.symm.trans (hxEq.trans hxEnd)
    norm_num at this
  have hsndSupport : W.snd ∈ W.support :=
    List.mem_of_mem_tail (W.snd_mem_tail_support hnil)
  have hsndVertices : W.snd ∈
      rlc_pathVertices rlc_traceSplitCounterexampleRight.1 :=
    rlc_ambientCrossingWalk_support_mem_pathVertices
      rlc_traceSplitCounterexampleRight.1 hsndSupport
  rw [rlc_traceSplitCounterexample_right_vertices] at hsndVertices
  simp only [Finset.mem_insert, Finset.mem_singleton] at hsndVertices
  have hadj := W.adj_snd hnil
  change (hypercubicLattice 2).Adj
    (rlc_traceSplitCounterexampleRight.1.1 : Site 2) W.snd at hadj
  have hadj0 : (hypercubicLattice 2).Adj
      (![0, -1] : Site 2) W.snd := by
    simpa only [hstart] using hadj
  have hsnd : W.snd = (![1, -1] : Site 2) := by
    rcases hsndVertices with hsnd | hsnd | hsnd | hsnd
    · rw [hsnd] at hadj0
      simp at hadj0
    · exact hsnd
    · rw [hsnd, hypercubicLattice_adj, Fin.sum_univ_two] at hadj0
      norm_num at hadj0
    · rw [hsnd, hypercubicLattice_adj, Fin.sum_univ_two] at hadj0
      norm_num at hadj0
  have he := W.mk_start_snd_mem_edges hnil
  change s((rlc_traceSplitCounterexampleRight.1.1 : Site 2), W.snd) ∈
    W.edges at he
  have he' : s((![0, -1] : Site 2), ![1, -1]) ∈ W.edges := by
    simpa only [hstart, hsnd] using he
  exact rlc_ambientCrossingWalk_edge_mem_pathEdges
    rlc_traceSplitCounterexampleRight.1 he'

private theorem rlc_traceSplitCounterexample_boundaryArc_relaxed₀₁ :
    rlc_contourEdgeRelaxedLocal rlc_windingSideCounterexampleGap
      (![-1, -2] : Site 2) ![-1, -1] := by
  unfold rlc_contourEdgeRelaxedLocal
  right
  constructor
  · unfold rlc_reflectedTargetLocallySupported
    right
    left
    change rlc_edgeBoxIncidentGap rlc_windingSideCounterexampleGap
      s((![0, -1] : Site 2), ![0, 0])
    constructor
    · intro z hz
      rw [Sym2.mem_iff] at hz
      rcases hz with rfl | rfl <;> simp [mem_rect]
    · refine ⟨![0, 0], ?_, by simp⟩
      simpa [RlcAxisBarrierGap.seedVertex,
        rlc_windingSideCounterexampleGap] using
          (rlc_windingSideCounterexampleGap.seedVertex_mem_region_of_lt
            (by norm_num) (by change (-1 : ℤ) + 1 < 1; omega))
  · unfold rlc_boundarySourceLocallySupported
    right
    left
    unfold rlc_reflectedPathEdges
    rw [Finset.mem_image]
    refine ⟨s((![0, -1] : Site 2), ![1, -1]), ?_, ?_⟩
    · exact rlc_traceSplitCounterexample_right_first_edge
    · simp [sharedPrimalEdge, Sym2.map_mk, rlc_flipX, rlc_flipXFun]

private theorem rlc_traceSplitCounterexample_boundaryArc_relaxed₁₂ :
    rlc_contourEdgeRelaxedLocal rlc_windingSideCounterexampleGap
      (![-1, -1] : Site 2) ![0, -1] := by
  unfold rlc_contourEdgeRelaxedLocal
  right
  constructor
  · unfold rlc_reflectedTargetLocallySupported
    right
    left
    change rlc_edgeBoxIncidentGap rlc_windingSideCounterexampleGap
      s((![0, 0] : Site 2), ![1, 0])
    constructor
    · intro z hz
      rw [Sym2.mem_iff] at hz
      rcases hz with rfl | rfl <;> simp [mem_rect]
    · refine ⟨![0, 0], ?_, by simp⟩
      simpa [RlcAxisBarrierGap.seedVertex,
        rlc_windingSideCounterexampleGap] using
          (rlc_windingSideCounterexampleGap.seedVertex_mem_region_of_lt
            (by norm_num) (by change (-1 : ℤ) + 1 < 1; omega))
  · unfold rlc_boundarySourceLocallySupported
    left
    change rlc_edgeBoxIncidentGap rlc_windingSideCounterexampleGap
      s((![0, -1] : Site 2), ![0, 0])
    constructor
    · intro z hz
      rw [Sym2.mem_iff] at hz
      rcases hz with rfl | rfl <;> simp [mem_rect]
    · refine ⟨![0, 0], ?_, by simp⟩
      simpa [RlcAxisBarrierGap.seedVertex,
        rlc_windingSideCounterexampleGap] using
          (rlc_windingSideCounterexampleGap.seedVertex_mem_region_of_lt
            (by norm_num) (by change (-1 : ℤ) + 1 < 1; omega))

private theorem rlc_traceSplitCounterexample_boundaryArc_relaxed₂₃ :
    rlc_contourEdgeRelaxedLocal rlc_windingSideCounterexampleGap
      (![0, -1] : Site 2) ![1, -1] := by
  unfold rlc_contourEdgeRelaxedLocal
  right
  constructor
  · unfold rlc_reflectedTargetLocallySupported
    right
    left
    change rlc_edgeBoxIncidentGap rlc_windingSideCounterexampleGap
      s((![1, 0] : Site 2), ![2, 0])
    constructor
    · intro z hz
      rw [Sym2.mem_iff] at hz
      rcases hz with rfl | rfl <;> simp [mem_rect]
    · exact ⟨![1, 0],
        rlc_traceSplitCounterexample_one_zero_mem_axisGapRegion, by simp⟩
  · unfold rlc_boundarySourceLocallySupported
    left
    change rlc_edgeBoxIncidentGap rlc_windingSideCounterexampleGap
      s((![1, -1] : Site 2), ![1, 0])
    constructor
    · intro z hz
      rw [Sym2.mem_iff] at hz
      rcases hz with rfl | rfl <;> simp [mem_rect]
    · exact ⟨![1, 0],
        rlc_traceSplitCounterexample_one_zero_mem_axisGapRegion, by simp⟩

theorem rlc_traceSplitCounterexample_boundaryArc_relaxed
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hK : rlc_mixedWiredReachSet rlc_windingSideCounterexampleGap omega =
      (rlc_pathVertices rlc_traceSplitCounterexampleRight.1 : Set (Site 2))) :
    ∀ {f g : Site 2},
      s(f, g) ∈
          (rlc_traceSplitCounterexample_boundaryArc omega hK).edges →
        rlc_contourEdgeRelaxedLocal
          rlc_windingSideCounterexampleGap f g := by
  intro f g hfg
  rw [rlc_traceSplitCounterexample_boundaryArc_edges] at hfg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hfg
  rcases hfg with hfg | hfg | hfg
  · exact rlc_contourEdgeRelaxedLocal_of_mk_eq
      rlc_windingSideCounterexampleGap (latAdj_top (-1) (-2)) hfg
        rlc_traceSplitCounterexample_boundaryArc_relaxed₀₁
  · exact rlc_contourEdgeRelaxedLocal_of_mk_eq
      rlc_windingSideCounterexampleGap (latAdj_right (-1) (-1)) hfg
        rlc_traceSplitCounterexample_boundaryArc_relaxed₁₂
  · exact rlc_contourEdgeRelaxedLocal_of_mk_eq
      rlc_windingSideCounterexampleGap (latAdj_right 0 (-1)) hfg
        rlc_traceSplitCounterexample_boundaryArc_relaxed₂₃




theorem rlc_traceSplitCounterexample_not_defectCut_of_reachSet_eq
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hK : rlc_mixedWiredReachSet rlc_windingSideCounterexampleGap omega =
      (rlc_pathVertices rlc_traceSplitCounterexampleRight.1 : Set (Site 2))) :
    ¬ RlcRelaxedLocalDefectsSeparateTraces
      rlc_windingSideCounterexampleGap omega := by
  intro hcut
  let a := rlc_traceSplitCounterexample_boundaryArc omega hK
  obtain ⟨f, g, hfg, hbad⟩ := hcut a
    rlc_traceSplitCounterexample_boundaryArc_rightContact
    rlc_traceSplitCounterexample_boundaryArc_leftContact
  exact hbad (rlc_traceSplitCounterexample_boundaryArc_relaxed omega hK hfg)



theorem rlc_windingSideCounterexample_not_defectCut :
    ¬ RlcRelaxedLocalDefectsSeparateTraces
      rlc_windingSideCounterexampleGap
      rlc_windingSideCounterexampleConfig :=
  rlc_traceSplitCounterexample_not_defectCut_of_reachSet_eq
    rlc_windingSideCounterexampleConfig
    rlc_windingSideCounterexample_reachSet_eq




theorem rlc_axisOrContactCounterexample_not_defectCut :
    ¬ RlcRelaxedLocalDefectsSeparateTraces
      rlc_windingSideCounterexampleGap
      rlc_axisOrContactCounterexampleConfig :=
  rlc_traceSplitCounterexample_not_defectCut_of_reachSet_eq
    rlc_axisOrContactCounterexampleConfig
    rlc_axisOrContactCounterexample_reachSet_eq



theorem rlc_axisOrContactCounterexample_dual_success :
    rlc_dualReflectConfig rlc_axisOrContactCounterexampleConfig ∈
      rlc_mixedWiredConnectorEvent rlc_windingSideCounterexampleGap := by
  exact rlc_mixedWiredConnectorEvent_dualReflect_of_not_defectCut
    rlc_windingSideCounterexampleGap (by norm_num)
      (by change (-1 : ℤ) + 1 < 1; omega)
      rlc_axisOrContactCounterexampleConfig
      rlc_axisOrContactCounterexample_not_defectCut

end Universality
end StatMech
