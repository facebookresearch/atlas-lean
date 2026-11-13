/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Universality.RSWArcBadPlacement


















open Function MeasureTheory Set

namespace StatMech
namespace Universality

open StatMech.Percolation
open StatMech.Lattice
open StatMech.RSW.Box



def RlcFaceBoundaryWalkSourceSupported {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (omega : ConfigSpace (Sym2 (Site 2))) {x y : Site 2}
    (c : (faceBoundaryGraph
      (rlc_mixedWiredReachSet G omega)).Walk x y) : Prop :=
  ∀ {f g : Site 2}, s(f, g) ∈ c.edges →
    sharedPrimalEdge f g ∈ rlc_mixedAxisGapEdges G




theorem rlc_mixedWired_reflected_faceBoundaryEdge_open_raw_of_sourceSupported
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2))) {f g : Site 2}
    (hfg : (faceBoundaryGraph
      (rlc_mixedWiredReachSet G omega)).Adj f g)
    (hsource : sharedPrimalEdge f g ∈ rlc_mixedAxisGapEdges G) :
    rlc_dualReflectConfig omega
      s(rlc_dualReflect f, rlc_dualReflect g) = true := by
  have hpims : rlc_pimsEdgeEquiv
      s(rlc_dualReflect f, rlc_dualReflect g) =
        sharedPrimalEdge f g :=
    rlc_pimsEdgeEquiv_reflected_faceBoundaryEdge
      (rlc_mixedWiredReachSet G omega) hfg
  have hnotExposed : rlc_pimsEdgeEquiv
      s(rlc_dualReflect f, rlc_dualReflect g) ∉
        rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1 :=
    rlc_mixedWired_faceBoundary_preimage_not_exposed
      G hn hlt omega hfg
  have hsource' : rlc_pimsEdgeEquiv
      s(rlc_dualReflect f, rlc_dualReflect g) ∈
        rlc_mixedAxisGapEdges G := by
    rw [hpims]
    exact hsource
  have hclosed := rlc_mixedWired_faceBoundary_preimage_closed
    G hn hlt omega hfg
  have hrawClosed : omega (rlc_pimsEdgeEquiv
      s(rlc_dualReflect f, rlc_dualReflect g)) = false := by
    rw [rlc_wiredConnectorConfig, if_neg hnotExposed,
      rlc_maskConfig, if_pos hsource'] at hclosed
    exact hclosed
  rw [rlc_dualReflectConfig_eq_pims, hrawClosed]
  rfl




theorem rlc_mixedWired_reflected_faceBoundaryEdge_open_raw_or_sourceDefect
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2))) {f g : Site 2}
    (hfg : (faceBoundaryGraph
      (rlc_mixedWiredReachSet G omega)).Adj f g) :
    rlc_dualReflectConfig omega
        s(rlc_dualReflect f, rlc_dualReflect g) = true ∨
      sharedPrimalEdge f g ∉ rlc_mixedAxisGapEdges G := by
  by_cases hsource : sharedPrimalEdge f g ∈ rlc_mixedAxisGapEdges G
  · exact Or.inl
      (rlc_mixedWired_reflected_faceBoundaryEdge_open_raw_of_sourceSupported
        G hn hlt omega hfg hsource)
  · exact Or.inr hsource





theorem rlc_dualReflect_raw_faceBoundaryWalk_of_sourceSupported
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2))) {x y : Site 2}
    (c : (faceBoundaryGraph
      (rlc_mixedWiredReachSet G omega)).Walk x y)
    (hsource : RlcFaceBoundaryWalkSourceSupported G omega c) :
    ∃ q : (openSubgraph 2 (rlc_dualReflectConfig omega)).Walk
        (rlc_dualReflect x) (rlc_dualReflect y),
      q.edges = (rlc_dualReflectOpenWalk
        (rlc_wiredConnectorConfig gamma gamma'
          (rlc_mixedAxisGapEdges G) omega)
        (c.mapLe (rlc_mixedWiredFaceBoundaryGraph_le_openFaceDual
          G hn hlt omega))).edges ∧
      q.support = (rlc_dualReflectOpenWalk
        (rlc_wiredConnectorConfig gamma gamma'
          (rlc_mixedAxisGapEdges G) omega)
        (c.mapLe (rlc_mixedWiredFaceBoundaryGraph_le_openFaceDual
          G hn hlt omega))).support := by
  let eta := rlc_wiredConnectorConfig gamma gamma'
    (rlc_mixedAxisGapEdges G) omega
  let hle := rlc_mixedWiredFaceBoundaryGraph_le_openFaceDual
    G hn hlt omega
  let p := rlc_dualReflectOpenWalk eta (c.mapLe hle)
  let H := openSubgraph 2 (rlc_dualReflectConfig omega)
  have htransfer : ∀ e ∈ p.edges, e ∈ H.edgeSet := by
    intro e he
    have hEdges : p.edges =
        (c.mapLe hle).edges.map
          (Sym2.map (rlc_dualReflectOpenHom eta)) :=
      SimpleGraph.Walk.edges_map
        (rlc_dualReflectOpenHom eta) (c.mapLe hle)
    rw [hEdges] at he
    obtain ⟨e0, he0, rfl⟩ := List.mem_map.mp he
    induction e0 using Sym2.inductionOn with
    | _ f g =>
        have hfgEdge : s(f, g) ∈ c.edges := by
          rw [c.edges_mapLe_eq_edges hle] at he0
          exact he0
        have hfg : (faceBoundaryGraph
            (rlc_mixedWiredReachSet G omega)).Adj f g :=
          c.adj_of_mem_edges hfgEdge
        change s(rlc_dualReflect f, rlc_dualReflect g) ∈ H.edgeSet
        rw [SimpleGraph.mem_edgeSet, openSubgraph_adj]
        refine ⟨(rlc_adj_dualReflect f g).mp hfg.1, ?_⟩
        exact
          rlc_mixedWired_reflected_faceBoundaryEdge_open_raw_of_sourceSupported
            G hn hlt omega hfg (hsource hfgEdge)
  let q := p.transfer H htransfer
  exact ⟨q, p.edges_transfer htransfer, p.support_transfer htransfer⟩




theorem rlc_dualReflectOpenWalk_edge_not_mem_of_edge_not_mem
    (S : Set (Site 2)) (eta : ConfigSpace (Sym2 (Site 2)))
    {x y : Site 2} (c : (faceBoundaryGraph S).Walk x y)
    (hle : faceBoundaryGraph S ≤
      openSubgraph 2 (fci_faceDualConfig eta))
    {e : Sym2 (Site 2)} (he : e ∉ c.edges) :
    rlc_dualReflectEdge e ∉
      (rlc_dualReflectOpenWalk eta (c.mapLe hle)).edges := by
  intro hreflected
  unfold rlc_dualReflectOpenWalk at hreflected
  have hEdges := SimpleGraph.Walk.edges_map
    (rlc_dualReflectOpenHom eta) (c.mapLe hle)
  have hreflected' : rlc_dualReflectEdge e ∈
      (c.mapLe hle).edges.map
        (Sym2.map (rlc_dualReflectOpenHom eta)) := by
    exact hEdges ▸ hreflected
  obtain ⟨e0, he0, heq⟩ := List.mem_map.mp hreflected'
  have he0c : e0 ∈ c.edges := by
    simpa only [SimpleGraph.Walk.edges_mapLe_eq_edges] using he0
  have hmap : Sym2.map (rlc_dualReflectOpenHom eta) e0 =
      rlc_dualReflectEdge e0 := by
    induction e0 using Sym2.inductionOn with
    | _ f g => rfl
  have heq' : rlc_dualReflectEdge e0 = rlc_dualReflectEdge e := by
    rw [← hmap]
    exact heq
  exact he (rlc_dualReflectEdge.injective heq' ▸ he0c)



theorem rlc_mixedWiredReachSet_faceBoundaryComplementaryArc_with_anchorAdj
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hno : omega ∉ rlc_mixedWiredConnectorEvent G) :
    ∃ (t : ℤ) (f g : Site 2),
      G.lower ≤ t ∧ t < G.upper ∧
      ![0, t] ∈ rlc_mixedWiredReachSet G omega ∧
      ![0, t + 1] ∉ rlc_mixedWiredReachSet G omega ∧
      (faceBoundaryGraph
        (rlc_mixedWiredReachSet G omega)).Adj f g ∧
      sharedPrimalEdge f g = s(![0, t], ![0, t + 1]) ∧
      ∃ p : (faceBoundaryGraph
        (rlc_mixedWiredReachSet G omega)).Walk f g,
        s(f, g) ∉ p.edges := by
  obtain ⟨t, f, g, u, c, htLower, htUpper, htIn, htOut,
      hfg, hshared, hcycle, hedge⟩ :=
    rlc_mixedWiredReachSet_axis_anchored_dualCircuit G omega hno
  let B := faceBoundaryGraph (rlc_mixedWiredReachSet G omega)
  have hreach : (B.deleteEdges {s(f, g)}).Reachable f g :=
    (SimpleGraph.adj_and_reachable_delete_edges_iff_exists_cycle
      (G := B)).mpr ⟨u, c, hcycle, hedge⟩ |>.2
  obtain ⟨p, hp⟩ :=
    (SimpleGraph.reachable_deleteEdges_iff_exists_walk (G := B)).mp hreach
  exact ⟨t, f, g, htLower, htUpper, htIn, htOut,
    hfg, hshared, p, hp⟩






theorem rlc_mixedWiredFailure_faceBoundaryArc_sourceNormalForm
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hno : omega ∉ rlc_mixedWiredConnectorEvent G) :
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
      s(![0, t], ![0, t + 1]) ∈ rlc_mixedAxisGapEdges G ∧
      omega s(![0, t], ![0, t + 1]) = false ∧
      rlc_dualReflectConfig omega
        s(![-1, t + 1], ![0, t + 1]) = true ∧
      ∀ {a b : Site 2}, s(a, b) ∈ p.edges →
        rlc_pimsEdgeEquiv
            s(rlc_dualReflect a, rlc_dualReflect b) =
              sharedPrimalEdge a b ∧
        rlc_wiredConnectorConfig gamma gamma'
            (rlc_mixedAxisGapEdges G) omega
            (rlc_pimsEdgeEquiv
              s(rlc_dualReflect a, rlc_dualReflect b)) = false ∧
        rlc_pimsEdgeEquiv
            s(rlc_dualReflect a, rlc_dualReflect b) ∉
              rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1 ∧
        (rlc_pimsEdgeEquiv
              s(rlc_dualReflect a, rlc_dualReflect b) ∈
                rlc_mixedAxisGapEdges G ↔
          sharedPrimalEdge a b ∈ rlc_axisGapEdges G ∨
          sharedPrimalEdge a b ∈ rlc_reflectedPathEdges gamma.1 ∨
          sharedPrimalEdge a b ∈ rlc_reflectedPathEdges gamma'.1) := by
  obtain ⟨t, f, g, htLower, htUpper, htIn, htOut,
      hfg, hshared, p, hanchor⟩ :=
    rlc_mixedWiredReachSet_faceBoundaryComplementaryArc_with_anchorAdj
      G omega hno
  let e : Sym2 (Site 2) := s(![0, t], ![0, t + 1])
  have hU : e ∈ rlc_mixedAxisGapEdges G :=
    G.verticalEdge_mem_mixedAxisGapEdges hn hlt htLower htUpper
  have hnotPaths : e ∉
      rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1 := by
    intro he
    rw [Finset.mem_union] at he
    rcases he with he | he
    · exact (Finset.disjoint_left.mp
        (rlc_rightPathEdges_disjoint_mixedAxisGapEdges G)) he hU
    · exact (Finset.disjoint_left.mp
        (rlc_leftPathEdges_disjoint_mixedAxisGapEdges G)) he hU
  have hadj : (hypercubicLattice 2).Adj
      (![0, t] : Site 2) ![0, t + 1] := by
    simp [hypercubicLattice_adj, Fin.sum_univ_two]
  have hclosed := rlc_mixedWiredReachSet_boundary_closed
    G hn hlt omega htIn hadj htOut
  have homega : omega e = false := by
    change rlc_wiredConnectorConfig gamma gamma'
      (rlc_mixedAxisGapEdges G) omega e = false at hclosed
    rw [rlc_wiredConnectorConfig, if_neg hnotPaths,
      rlc_maskConfig, if_pos hU] at hclosed
    exact hclosed
  have hanchorOpen : rlc_dualReflectConfig omega
      s(![-1, t + 1], ![0, t + 1]) = true := by
    have hpims : rlc_pimsEdgeEquiv
        s(![-1, t + 1], ![0, t + 1]) = e := by
      simpa [e] using (rlc_pimsEdgeEquiv_horizontal (-1) (t + 1))
    rw [rlc_dualReflectConfig_eq_pims, hpims, homega]
    rfl
  refine ⟨t, f, g, p, htLower, htUpper, htIn, htOut,
    hfg, hshared, hanchor, hU, homega, hanchorOpen, ?_⟩
  intro a b hab
  have habAdj := p.adj_of_mem_edges hab
  refine ⟨rlc_pimsEdgeEquiv_reflected_faceBoundaryEdge
      (rlc_mixedWiredReachSet G omega) habAdj,
    rlc_mixedWired_faceBoundary_preimage_closed
      G hn hlt omega habAdj,
    rlc_mixedWired_faceBoundary_preimage_not_exposed
      G hn hlt omega habAdj, ?_⟩
  exact rlc_mixedWired_faceBoundary_preimage_mem_mixedAxisGapEdges_iff
    G hn hlt omega habAdj




theorem rlc_mixedWiredFailure_faceBoundaryArc_rawOpen_or_sourceDefect
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hno : omega ∉ rlc_mixedWiredConnectorEvent G) :
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
      ∀ {a b : Site 2}, s(a, b) ∈ p.edges →
        rlc_dualReflectConfig omega
            s(rlc_dualReflect a, rlc_dualReflect b) = true ∨
          sharedPrimalEdge a b ∉ rlc_mixedAxisGapEdges G := by
  obtain ⟨t, f, g, htLower, htUpper, htIn, htOut,
      hfg, hshared, p, hanchor⟩ :=
    rlc_mixedWiredReachSet_faceBoundaryComplementaryArc_with_anchorAdj
      G omega hno
  refine ⟨t, f, g, p, htLower, htUpper, htIn, htOut,
    hfg, hshared, hanchor, ?_⟩
  intro a b hab
  exact rlc_mixedWired_reflected_faceBoundaryEdge_open_raw_or_sourceDefect
    G hn hlt omega (p.adj_of_mem_edges hab)




theorem rlc_mixedWiredFailure_rawComplementaryArc_or_sourceDefect
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hno : omega ∉ rlc_mixedWiredConnectorEvent G) :
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
      ((∃ q : (openSubgraph 2 (rlc_dualReflectConfig omega)).Walk
          (rlc_dualReflect f) (rlc_dualReflect g),
          q.edges = (rlc_dualReflectOpenWalk
            (rlc_wiredConnectorConfig gamma gamma'
              (rlc_mixedAxisGapEdges G) omega)
            (p.mapLe (rlc_mixedWiredFaceBoundaryGraph_le_openFaceDual
              G hn hlt omega))).edges ∧
          q.support = (rlc_dualReflectOpenWalk
            (rlc_wiredConnectorConfig gamma gamma'
              (rlc_mixedAxisGapEdges G) omega)
            (p.mapLe (rlc_mixedWiredFaceBoundaryGraph_le_openFaceDual
              G hn hlt omega))).support ∧
          s(rlc_dualReflect f, rlc_dualReflect g) ∉ q.edges) ∨
        ∃ a b : Site 2, s(a, b) ∈ p.edges ∧
          sharedPrimalEdge a b ∉ rlc_mixedAxisGapEdges G) := by
  classical
  obtain ⟨t, f, g, htLower, htUpper, htIn, htOut,
      hfg, hshared, p, hanchor⟩ :=
    rlc_mixedWiredReachSet_faceBoundaryComplementaryArc_with_anchorAdj
      G omega hno
  refine ⟨t, f, g, p, htLower, htUpper, htIn, htOut,
    hfg, hshared, hanchor, ?_⟩
  by_cases hsource : RlcFaceBoundaryWalkSourceSupported G omega p
  · obtain ⟨q, hqEdges, hqSupport⟩ :=
      rlc_dualReflect_raw_faceBoundaryWalk_of_sourceSupported
        G hn hlt omega p hsource
    refine Or.inl ⟨q, hqEdges, hqSupport, ?_⟩
    rw [hqEdges]
    simpa [rlc_dualReflectEdge, Sym2.map_mk] using
      (rlc_dualReflectOpenWalk_edge_not_mem_of_edge_not_mem
        (rlc_mixedWiredReachSet G omega)
        (rlc_wiredConnectorConfig gamma gamma'
          (rlc_mixedAxisGapEdges G) omega)
        p (rlc_mixedWiredFaceBoundaryGraph_le_openFaceDual
          G hn hlt omega) hanchor)
  · right
    unfold RlcFaceBoundaryWalkSourceSupported at hsource
    push Not at hsource
    exact hsource







theorem rlc_dualReflect_wired_faceBoundaryWalk_of_relaxedLocal
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2))) {x y : Site 2}
    (c : (faceBoundaryGraph
      (rlc_mixedWiredReachSet G omega)).Walk x y)
    (hlocal : ∀ {f g : Site 2}, s(f, g) ∈ c.edges →
      rlc_contourEdgeRelaxedLocal G f g) :
    ∃ q : (openSubgraph 2
      (rlc_wiredConnectorConfig gamma gamma' (rlc_mixedAxisGapEdges G)
        (rlc_dualReflectConfig omega))).Walk
        (rlc_dualReflect x) (rlc_dualReflect y),
      q.edges = (rlc_dualReflectOpenWalk
        (rlc_wiredConnectorConfig gamma gamma'
          (rlc_mixedAxisGapEdges G) omega)
        (c.mapLe (rlc_mixedWiredFaceBoundaryGraph_le_openFaceDual
          G hn hlt omega))).edges ∧
      q.support = (rlc_dualReflectOpenWalk
        (rlc_wiredConnectorConfig gamma gamma'
          (rlc_mixedAxisGapEdges G) omega)
        (c.mapLe (rlc_mixedWiredFaceBoundaryGraph_le_openFaceDual
          G hn hlt omega))).support := by
  apply rlc_dualReflect_wired_faceBoundaryWalk_of_relaxed_support
    G hn hlt omega c
  intro f g hfgEdge
  rcases hlocal hfgEdge with hexposed | hpaired
  · exact Or.inl hexposed
  · have hfg := c.adj_of_mem_edges hfgEdge
    obtain ⟨htarget, hsource⟩ :=
      rlc_mixedWired_reflected_faceBoundaryEdge_support_of_local
        G hn hlt omega hfg hpaired.1 hpaired.2
    rw [Finset.mem_union] at htarget
    rcases htarget with hexposed | hfresh
    · exact Or.inl hexposed
    · have hsource' := hsource
      rw [rlc_pimsEdgeEquiv_reflected_faceBoundaryEdge
        (rlc_mixedWiredReachSet G omega) hfg] at hsource'
      exact Or.inr ⟨hfresh, hsource'⟩






theorem rlc_mixedWiredFailure_wiredComplementaryArc_or_relaxedLocalDefect
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hno : omega ∉ rlc_mixedWiredConnectorEvent G) :
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
      ((∃ q : (openSubgraph 2
          (rlc_wiredConnectorConfig gamma gamma'
            (rlc_mixedAxisGapEdges G)
            (rlc_dualReflectConfig omega))).Walk
            (rlc_dualReflect f) (rlc_dualReflect g),
          q.edges = (rlc_dualReflectOpenWalk
            (rlc_wiredConnectorConfig gamma gamma'
              (rlc_mixedAxisGapEdges G) omega)
            (p.mapLe (rlc_mixedWiredFaceBoundaryGraph_le_openFaceDual
              G hn hlt omega))).edges ∧
          q.support = (rlc_dualReflectOpenWalk
            (rlc_wiredConnectorConfig gamma gamma'
              (rlc_mixedAxisGapEdges G) omega)
            (p.mapLe (rlc_mixedWiredFaceBoundaryGraph_le_openFaceDual
              G hn hlt omega))).support ∧
          s(rlc_dualReflect f, rlc_dualReflect g) ∉ q.edges) ∨
        ∃ a b : Site 2, s(a, b) ∈ p.edges ∧
          ¬ rlc_contourEdgeRelaxedLocal G a b) := by
  classical
  obtain ⟨t, f, g, htLower, htUpper, htIn, htOut,
      hfg, hshared, p, hanchor⟩ :=
    rlc_mixedWiredReachSet_faceBoundaryComplementaryArc_with_anchorAdj
      G omega hno
  refine ⟨t, f, g, p, htLower, htUpper, htIn, htOut,
    hfg, hshared, hanchor, ?_⟩
  by_cases hlocal : ∀ {a b : Site 2}, s(a, b) ∈ p.edges →
      rlc_contourEdgeRelaxedLocal G a b
  · obtain ⟨q, hqEdges, hqSupport⟩ :=
      rlc_dualReflect_wired_faceBoundaryWalk_of_relaxedLocal
        G hn hlt omega p hlocal
    refine Or.inl ⟨q, hqEdges, hqSupport, ?_⟩
    rw [hqEdges]
    simpa [rlc_dualReflectEdge, Sym2.map_mk] using
      (rlc_dualReflectOpenWalk_edge_not_mem_of_edge_not_mem
        (rlc_mixedWiredReachSet G omega)
        (rlc_wiredConnectorConfig gamma gamma'
          (rlc_mixedAxisGapEdges G) omega)
        p (rlc_mixedWiredFaceBoundaryGraph_le_openFaceDual
          G hn hlt omega) hanchor)
  · right
    push Not at hlocal
    exact hlocal

end Universality
end StatMech
