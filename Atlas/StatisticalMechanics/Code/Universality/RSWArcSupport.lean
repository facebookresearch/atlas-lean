/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Universality.RSWLowestCrossing















open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators

namespace StatMech
namespace Universality

open StatMech.Percolation
open StatMech.Lattice
open StatMech.RSW.Box






theorem rlc_mixedWiredConnectorEvent_of_openWalk_meets_paths {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (omega : ConfigSpace (Sym2 (Site 2))) {a b : Site 2}
    (q : (openSubgraph 2
      (rlc_wiredConnectorConfig gamma gamma' (rlc_mixedAxisGapEdges G)
        omega)).Walk a b)
    (hbox : ∀ z ∈ q.support,
      z ∈ rlc_connectorBox n)
    (hright : ∃ x ∈ q.support, x ∈ rlc_pathVertices gamma.1)
    (hleft : ∃ y ∈ q.support, y ∈ rlc_pathVertices gamma'.1) :
    omega ∈ rlc_mixedWiredConnectorEvent G := by
  obtain ⟨x, hxq, hxPath⟩ := hright
  obtain ⟨y, hyq, hyPath⟩ := hleft
  let eta := rlc_wiredConnectorConfig gamma gamma'
    (rlc_mixedAxisGapEdges G) omega
  let qxy : (openSubgraph 2 eta).Walk x y :=
    (q.takeUntil x hxq).reverse.append (q.takeUntil y hyq)
  have hqxySub : ∀ z ∈ qxy.support, z ∈ q.support := by
    intro z hz
    dsimp only [qxy] at hz
    rw [SimpleGraph.Walk.support_append,
      SimpleGraph.Walk.support_reverse] at hz
    rcases List.mem_append.mp hz with hz | hz
    · rw [List.mem_reverse] at hz
      exact q.support_takeUntil_subset_support hxq hz
    · exact q.support_takeUntil_subset_support hyq
        (List.mem_of_mem_tail hz)
  have hqxyBox : ∀ z ∈ qxy.support,
      z ∈ rect (-2 * n) (2 * n) (-n) n :=
    fun z hz => by
      simpa [rlc_connectorBox] using hbox z (hqxySub z hz)
  have hxR : x ∈ rect (-2 * n) (2 * n) (-n) n :=
    by simpa [rlc_connectorBox] using hbox x hxq
  have hyR : y ∈ rect (-2 * n) (2 * n) (-n) n :=
    by simpa [rlc_connectorBox] using hbox y hyq
  have hxy : ConnectedWithin 2 eta
      (rect (-2 * n) (2 * n) (-n) n) ⟨x, hxR⟩ ⟨y, hyR⟩ := by
    exact ⟨qxy.induce (rect (-2 * n) (2 * n) (-n) n) hqxyBox⟩
  have hrightOpen : eta ∈ rlc_pathOpen gamma.1 :=
    rlc_wiredConnectorConfig_rightPathOpen gamma gamma'
      (rlc_mixedAxisGapEdges G) omega
  have hleftOpen : eta ∈ rlc_pathOpen gamma'.1 :=
    rlc_wiredConnectorConfig_leftPathOpen gamma gamma'
      (rlc_mixedAxisGapEdges G) omega
  obtain ⟨_hlowerR, hstartLower⟩ :=
    rlc_pathOpen_connected_start gamma.1 eta hrightOpen
      G.lowerVertex_mem_right
  obtain ⟨_hxSmall, hstartX⟩ :=
    rlc_pathOpen_connected_start gamma.1 eta hrightOpen hxPath
  obtain ⟨_hySmall, hleftStartY⟩ :=
    rlc_pathOpen_connected_start gamma'.1 eta hleftOpen hyPath
  obtain ⟨_hupperR, hleftStartUpper⟩ :=
    rlc_pathOpen_connected_start gamma'.1 eta hleftOpen
      G.upperVertex_mem_left
  have hrightSub : rect 0 (2 * n) (-n) n ⊆
      rect (-2 * n) (2 * n) (-n) n := by
    intro z hz
    rw [mem_rect] at hz ⊢
    omega
  have hleftSub : rect (-2 * n) 0 (-n) n ⊆
      rect (-2 * n) (2 * n) (-n) n := by
    intro z hz
    rw [mem_rect] at hz ⊢
    omega
  have hlowerFull : G.lowerVertex ∈
      rect (-2 * n) (2 * n) (-n) n :=
    rlc_rightPathVertex_mem_connectorBox gamma G.lowerVertex_mem_right
  have hupperFull : G.upperVertex ∈
      rect (-2 * n) (2 * n) (-n) n :=
    rlc_leftPathVertex_mem_connectorBox gamma' G.upperVertex_mem_left
  have hlowerX : ConnectedWithin 2 eta
      (rect (-2 * n) (2 * n) (-n) n)
      ⟨G.lowerVertex, hlowerFull⟩ ⟨x, hxR⟩ := by
    simpa only using
      (StatMech.RSW.Strip.connectedWithin_mono_set eta hrightSub
        hstartLower).symm.trans
          (StatMech.RSW.Strip.connectedWithin_mono_set eta hrightSub hstartX)
  have hyUpper : ConnectedWithin 2 eta
      (rect (-2 * n) (2 * n) (-n) n)
      ⟨y, hyR⟩ ⟨G.upperVertex, hupperFull⟩ := by
    simpa only using
      (StatMech.RSW.Strip.connectedWithin_mono_set eta hleftSub
        hleftStartY).symm.trans
          (StatMech.RSW.Strip.connectedWithin_mono_set eta hleftSub
            hleftStartUpper)
  exact hlowerX.trans (hxy.trans hyUpper)





theorem rlc_dualReflect_wired_open_of_relaxed_support {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (omega : ConfigSpace (Sym2 (Site 2))) {e : Sym2 (Site 2)}
    (hsupport :
      e ∈ rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1 ∨
        (e ∈ rlc_mixedAxisGapEdges G ∧
          rlc_pimsEdgeEquiv e ∈ rlc_mixedAxisGapEdges G))
    (hopen : rlc_dualReflectConfig
      (rlc_wiredConnectorConfig gamma gamma'
        (rlc_mixedAxisGapEdges G) omega) e = true) :
    rlc_wiredConnectorConfig gamma gamma' (rlc_mixedAxisGapEdges G)
      (rlc_dualReflectConfig omega) e = true := by
  rcases hsupport with hexposed | hfresh
  · simp [rlc_wiredConnectorConfig, hexposed]
  · exact rlc_dualReflect_wired_open_of_support G omega
      (by simp [hfresh.1]) hfresh.2 hopen



theorem rlc_dualReflect_wired_walk_of_relaxed_support {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (omega : ConfigSpace (Sym2 (Site 2))) {x y : Site 2}
    (p : (openSubgraph 2 (rlc_dualReflectConfig
      (rlc_wiredConnectorConfig gamma gamma'
        (rlc_mixedAxisGapEdges G) omega))).Walk x y)
    (hsupport : ∀ e ∈ p.edges,
      e ∈ rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1 ∨
        (e ∈ rlc_mixedAxisGapEdges G ∧
          rlc_pimsEdgeEquiv e ∈ rlc_mixedAxisGapEdges G)) :
    ∃ q : (openSubgraph 2
      (rlc_wiredConnectorConfig gamma gamma' (rlc_mixedAxisGapEdges G)
        (rlc_dualReflectConfig omega))).Walk x y,
      q.edges = p.edges ∧ q.support = p.support := by
  let H := openSubgraph 2
    (rlc_wiredConnectorConfig gamma gamma' (rlc_mixedAxisGapEdges G)
      (rlc_dualReflectConfig omega))
  have htransfer : ∀ e ∈ p.edges, e ∈ H.edgeSet := by
    intro e he
    induction e using Sym2.inductionOn with
    | _ u v =>
        have hadj := p.adj_of_mem_edges he
        rw [openSubgraph_adj] at hadj
        rw [SimpleGraph.mem_edgeSet, openSubgraph_adj]
        exact ⟨hadj.1,
          rlc_dualReflect_wired_open_of_relaxed_support
            G omega (hsupport s(u, v) he) hadj.2⟩
  let q := p.transfer H htransfer
  exact ⟨q, p.edges_transfer htransfer, p.support_transfer htransfer⟩



theorem rlc_pimsEdgeEquiv_reflected_faceBoundaryEdge
    (S : Set (Site 2)) {f g : Site 2}
    (hfg : (faceBoundaryGraph S).Adj f g) :
    rlc_pimsEdgeEquiv s(rlc_dualReflect f, rlc_dualReflect g) =
      sharedPrimalEdge f g := by
  exact rlc_pimsEdgeEquiv_reflected_mk_of_adj hfg.1



theorem rlc_mixedWired_faceBoundary_preimage_closed {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2))) {f g : Site 2}
    (hfg : (faceBoundaryGraph
      (rlc_mixedWiredReachSet G omega)).Adj f g) :
    rlc_wiredConnectorConfig gamma gamma' (rlc_mixedAxisGapEdges G) omega
      (rlc_pimsEdgeEquiv
        s(rlc_dualReflect f, rlc_dualReflect g)) = false := by
  rw [rlc_pimsEdgeEquiv_reflected_faceBoundaryEdge
    (rlc_mixedWiredReachSet G omega) hfg]
  obtain ⟨p, q, hpq, hadj⟩ := sharedPrimalEdge_isLatticeEdge hfg.1
  have hpqBoundary : (p, q) ∈
      edgeBoundary 2 (rlc_mixedWiredReachSet G omega) := by
    refine ⟨hadj, ?_⟩
    rw [← bdEdge_mk]
    simpa [hpq] using hfg.2
  simpa [hpq] using
    (rlc_mixedWiredReachSet_edgeBoundary_closed
      G hn hlt omega hpqBoundary)




theorem rlc_mixedWired_faceBoundary_preimage_not_exposed {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2))) {f g : Site 2}
    (hfg : (faceBoundaryGraph
      (rlc_mixedWiredReachSet G omega)).Adj f g) :
    rlc_pimsEdgeEquiv s(rlc_dualReflect f, rlc_dualReflect g) ∉
      rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1 := by
  intro hexposed
  have hclosed := rlc_mixedWired_faceBoundary_preimage_closed
    G hn hlt omega hfg
  rw [rlc_wiredConnectorConfig, if_pos hexposed] at hclosed
  simp at hclosed






theorem rlc_mixedWired_faceBoundary_preimage_mem_mixedSupport_of_region_incident
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2))) {f g p q : Site 2}
    (hfg : (faceBoundaryGraph
      (rlc_mixedWiredReachSet G omega)).Adj f g)
    (hshared : sharedPrimalEdge f g = s(p, q))
    (hpR : p ∈ rect (-2 * n) (2 * n) (-n) n)
    (hqR : q ∈ rect (-2 * n) (2 * n) (-n) n)
    (hincident : p ∈ rlc_axisGapRegion G ∨
      q ∈ rlc_axisGapRegion G) :
    rlc_pimsEdgeEquiv s(rlc_dualReflect f, rlc_dualReflect g) ∈
      rlc_mixedAxisGapEdges G := by
  have hpBox : p ∈ rlc_connectorBox n := by
    simpa [rlc_connectorBox] using hpR
  have hqBox : q ∈ rlc_connectorBox n := by
    simpa [rlc_connectorBox] using hqR
  have hpqWithin : s(p, q) ∈
      edgesWithinFinset (rlc_connectorBox n) := by
    rw [mem_edgesWithinFinset]
    exact ⟨p, hpBox, q, hqBox, rfl⟩
  have hpqGap : s(p, q) ∈ rlc_axisGapEdges G := by
    rw [rlc_axisGapEdges, Finset.mem_union]
    apply Or.inl
    simp only [Finset.mem_filter]
    refine ⟨hpqWithin, ?_⟩
    rcases hincident with hp | hq
    · exact ⟨p, hp, Sym2.mem_mk_left p q⟩
    · exact ⟨q, hq, Sym2.mem_mk_right p q⟩
  rw [rlc_pimsEdgeEquiv_reflected_faceBoundaryEdge
    (rlc_mixedWiredReachSet G omega) hfg, hshared,
    rlc_mixedAxisGapEdges, Finset.mem_sdiff]
  refine ⟨?_, ?_⟩
  · simp only [Finset.mem_union]
    exact Or.inl (Or.inl hpqGap)
  · have hnot := rlc_mixedWired_faceBoundary_preimage_not_exposed
      G hn hlt omega hfg
    rw [rlc_pimsEdgeEquiv_reflected_faceBoundaryEdge
      (rlc_mixedWiredReachSet G omega) hfg] at hnot
    simpa [hshared] using hnot





theorem rlc_mixedWired_exists_faceBoundary_outside_transportSupport {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2))) :
    ∃ f g : Site 2,
      (faceBoundaryGraph (rlc_mixedWiredReachSet G omega)).Adj f g ∧
      s(rlc_dualReflect f, rlc_dualReflect g) ∉
        (rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1) ∪
          rlc_mixedAxisGapEdges G ∧
      rlc_pimsEdgeEquiv s(rlc_dualReflect f, rlc_dualReflect g) ∉
        rlc_mixedAxisGapEdges G := by
  let v : Site 2 := gamma.1.2.1
  let w : Site 2 := v + ![1, 0]
  have hvPath : v ∈ rlc_pathVertices gamma.1 := by
    simp only [rlc_pathVertices, Finset.mem_image, List.mem_toFinset]
    exact ⟨⟨v, by simpa [v] using rightSide_subset gamma.1.2.1.2⟩,
      gamma.1.2.2.1.end_mem_support, rfl⟩
  have hv : v ∈ rlc_mixedWiredReachSet G omega :=
    rlc_rightPathVertex_mem_mixedWiredReachSet G omega hvPath
  have hvx : v 0 = 2 * n := by
    simpa only [v] using gamma.1.2.1.2.2
  have hw0 : w 0 = v 0 + 1 := by
    change ((v + (![1, 0] : Site 2) : Site 2) 0) = v 0 + 1
    rw [Pi.add_apply]
    rfl
  have hw1 : w 1 = v 1 := by
    change ((v + (![1, 0] : Site 2) : Site 2) 1) = v 1
    rw [Pi.add_apply]
    simp
  have hadj : (hypercubicLattice 2).Adj v w := by
    rw [hypercubicLattice_adj, Fin.sum_univ_two, hw0, hw1]
    simp
  have hw : w ∉ rlc_mixedWiredReachSet G omega := by
    intro hwReach
    have hwR := rlc_mixedWiredReachSet_subset_box G omega hwReach
    rw [mem_rect] at hwR
    have : w 0 = 2 * n + 1 := by rw [hw0, hvx]
    omega
  have hvw : (v, w) ∈
      edgeBoundary 2 (rlc_mixedWiredReachSet G omega) :=
    ⟨hadj, iff_of_true hv hw⟩
  let f : Site 2 := ![v 0, v 1]
  let g : Site 2 := ![v 0, v 1 - 1]
  have hfgLat : (hypercubicLattice 2).Adj f g := by
    simp [f, g, hypercubicLattice_adj, Fin.sum_univ_two]
  have hshared : sharedPrimalEdge f g = s(v, w) := by
    change sharedPrimalEdge (![v 0, v 1] : Site 2)
      ![v 0, v 1 - 1] = s(v, w)
    rw [sharedPrimalEdge_bottom]
    unfold faceCorner00 faceCorner10
    have hev : (![v 0, v 1] : Site 2) = v := by
      ext i
      fin_cases i <;> simp
    have hew : (![v 0 + 1, v 1] : Site 2) = w := by
      ext i
      fin_cases i <;> simp [hw0, hw1]
    rw [hev, hew]
  have hfg : (faceBoundaryGraph
      (rlc_mixedWiredReachSet G omega)).Adj f g := by
    refine ⟨hfgLat, ?_⟩
    rw [hshared, bdEdge_mk]
    exact hvw.2
  refine ⟨f, g, hfg, ?_, ?_⟩
  intro htarget
  have hfR : rlc_dualReflect f ∈
      rect (-2 * n) (2 * n) (-n) n := by
    rw [Finset.mem_union] at htarget
    rcases htarget with hexposed | hmixed
    · exact (rlc_exposedPathEdges_endpoints_mem_box hexposed).1
    · exact (rlc_mixedAxisGapEdges_endpoints_mem_box
        G hn hlt hmixed).1
  rw [mem_rect] at hfR
  have hf0 : rlc_dualReflect f 0 = -2 * n - 1 := by
    simp [f, hvx]
  omega
  rw [rlc_pimsEdgeEquiv_reflected_faceBoundaryEdge
    (rlc_mixedWiredReachSet G omega) hfg, hshared]
  intro hU
  have hwR := (rlc_mixedAxisGapEdges_endpoints_mem_box
    G hn hlt hU).2
  rw [mem_rect] at hwR
  have : w 0 = 2 * n + 1 := by rw [hw0, hvx]
  omega




theorem rlc_mixedWiredReachSet_faceBoundaryComplementaryArc {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hno : omega ∉ rlc_mixedWiredConnectorEvent G) :
    ∃ (t : ℤ) (f g : Site 2),
      G.lower ≤ t ∧ t < G.upper ∧
      ![0, t] ∈ rlc_mixedWiredReachSet G omega ∧
      ![0, t + 1] ∉ rlc_mixedWiredReachSet G omega ∧
      sharedPrimalEdge f g = s(![0, t], ![0, t + 1]) ∧
      ∃ p : (faceBoundaryGraph
        (rlc_mixedWiredReachSet G omega)).Walk f g,
        s(f, g) ∉ p.edges := by
  obtain ⟨t, f, g, u, c, htlower, htupper, htIn, htOut,
      hfg, hshared, hcyc, hedge⟩ :=
    rlc_mixedWiredReachSet_axis_anchored_dualCircuit G omega hno
  let B := faceBoundaryGraph (rlc_mixedWiredReachSet G omega)
  have hreach : (B.deleteEdges {s(f, g)}).Reachable f g :=
    (SimpleGraph.adj_and_reachable_delete_edges_iff_exists_cycle
      (G := B)).mpr ⟨u, c, hcyc, hedge⟩ |>.2
  obtain ⟨p, hp⟩ :=
    (SimpleGraph.reachable_deleteEdges_iff_exists_walk (G := B)).mp hreach
  exact ⟨t, f, g, htlower, htupper, htIn, htOut, hshared, p, hp⟩










theorem rlc_dualReflect_wired_faceBoundaryWalk_of_support {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2))) {x y : Site 2}
    (c : (faceBoundaryGraph
      (rlc_mixedWiredReachSet G omega)).Walk x y)
    (htarget : ∀ {f g : Site 2}, s(f, g) ∈ c.edges →
      s(rlc_dualReflect f, rlc_dualReflect g) ∈
        (rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1) ∪
          rlc_mixedAxisGapEdges G)
    (hsource : ∀ {f g : Site 2}, s(f, g) ∈ c.edges →
      sharedPrimalEdge f g ∈ rlc_mixedAxisGapEdges G) :
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
  let eta := rlc_wiredConnectorConfig gamma gamma'
    (rlc_mixedAxisGapEdges G) omega
  let hle := rlc_mixedWiredFaceBoundaryGraph_le_openFaceDual
    G hn hlt omega
  let p := rlc_dualReflectOpenWalk eta (c.mapLe hle)
  apply rlc_dualReflect_wired_walk_of_support G omega p
  intro e he
  have hEdges : p.edges =
      (c.mapLe hle).edges.map
        (Sym2.map (rlc_dualReflectOpenHom eta)) :=
    SimpleGraph.Walk.edges_map (rlc_dualReflectOpenHom eta) (c.mapLe hle)
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
      refine ⟨htarget hfgEdge, ?_⟩
      change rlc_pimsEdgeEquiv
        s(rlc_dualReflect f, rlc_dualReflect g) ∈
          rlc_mixedAxisGapEdges G
      rw [rlc_pimsEdgeEquiv_reflected_faceBoundaryEdge
        (rlc_mixedWiredReachSet G omega) hfg]
      exact hsource hfgEdge




theorem rlc_dualReflect_wired_faceBoundaryWalk_of_relaxed_support {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2))) {x y : Site 2}
    (c : (faceBoundaryGraph
      (rlc_mixedWiredReachSet G omega)).Walk x y)
    (hsupport : ∀ {f g : Site 2}, s(f, g) ∈ c.edges →
      s(rlc_dualReflect f, rlc_dualReflect g) ∈
          rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1 ∨
        (s(rlc_dualReflect f, rlc_dualReflect g) ∈
            rlc_mixedAxisGapEdges G ∧
          sharedPrimalEdge f g ∈ rlc_mixedAxisGapEdges G)) :
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
  let eta := rlc_wiredConnectorConfig gamma gamma'
    (rlc_mixedAxisGapEdges G) omega
  let hle := rlc_mixedWiredFaceBoundaryGraph_le_openFaceDual
    G hn hlt omega
  let p := rlc_dualReflectOpenWalk eta (c.mapLe hle)
  apply rlc_dualReflect_wired_walk_of_relaxed_support G omega p
  intro e he
  have hEdges : p.edges =
      (c.mapLe hle).edges.map
        (Sym2.map (rlc_dualReflectOpenHom eta)) :=
    SimpleGraph.Walk.edges_map (rlc_dualReflectOpenHom eta) (c.mapLe hle)
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
      rcases hsupport hfgEdge with hexposed | hfresh
      · exact Or.inl hexposed
      · refine Or.inr ⟨hfresh.1, ?_⟩
        change rlc_pimsEdgeEquiv
          s(rlc_dualReflect f, rlc_dualReflect g) ∈
            rlc_mixedAxisGapEdges G
        rw [rlc_pimsEdgeEquiv_reflected_faceBoundaryEdge
          (rlc_mixedWiredReachSet G omega) hfg]
        exact hfresh.2




theorem rlc_dualReflect_wired_faceBoundaryWalk_of_relaxed_region_incident
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2))) {x y : Site 2}
    (c : (faceBoundaryGraph
      (rlc_mixedWiredReachSet G omega)).Walk x y)
    (hloc : ∀ {f g : Site 2}, s(f, g) ∈ c.edges →
      s(rlc_dualReflect f, rlc_dualReflect g) ∈
          rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1 ∨
        (s(rlc_dualReflect f, rlc_dualReflect g) ∈
            rlc_mixedAxisGapEdges G ∧
          ∃ p q : Site 2,
            sharedPrimalEdge f g = s(p, q) ∧
            p ∈ rect (-2 * n) (2 * n) (-n) n ∧
            q ∈ rect (-2 * n) (2 * n) (-n) n ∧
            (p ∈ rlc_axisGapRegion G ∨ q ∈ rlc_axisGapRegion G))) :
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
  rcases hloc hfgEdge with hexposed | hfresh
  · exact Or.inl hexposed
  · obtain ⟨htarget, p, q, hshared, hpR, hqR, hincident⟩ := hfresh
    refine Or.inr ⟨htarget, ?_⟩
    have hsource :=
      rlc_mixedWired_faceBoundary_preimage_mem_mixedSupport_of_region_incident
        G hn hlt omega (c.adj_of_mem_edges hfgEdge)
        hshared hpR hqR hincident
    rw [rlc_pimsEdgeEquiv_reflected_faceBoundaryEdge
      (rlc_mixedWiredReachSet G omega)
      (c.adj_of_mem_edges hfgEdge)] at hsource
    exact hsource





theorem rlc_mixedWiredConnectorEvent_dualReflect_of_faceBoundaryArc
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2))) {x y : Site 2}
    (c : (faceBoundaryGraph
      (rlc_mixedWiredReachSet G omega)).Walk x y)
    (hloc : ∀ {f g : Site 2}, s(f, g) ∈ c.edges →
      s(rlc_dualReflect f, rlc_dualReflect g) ∈
          rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1 ∨
        (s(rlc_dualReflect f, rlc_dualReflect g) ∈
            rlc_mixedAxisGapEdges G ∧
          ∃ p q : Site 2,
            sharedPrimalEdge f g = s(p, q) ∧
            p ∈ rect (-2 * n) (2 * n) (-n) n ∧
            q ∈ rect (-2 * n) (2 * n) (-n) n ∧
            (p ∈ rlc_axisGapRegion G ∨ q ∈ rlc_axisGapRegion G)))
    (hbox : ∀ z ∈ (rlc_dualReflectOpenWalk
      (rlc_wiredConnectorConfig gamma gamma'
        (rlc_mixedAxisGapEdges G) omega)
      (c.mapLe (rlc_mixedWiredFaceBoundaryGraph_le_openFaceDual
        G hn hlt omega))).support,
      z ∈ rlc_connectorBox n)
    (hright : ∃ z ∈ (rlc_dualReflectOpenWalk
      (rlc_wiredConnectorConfig gamma gamma'
        (rlc_mixedAxisGapEdges G) omega)
      (c.mapLe (rlc_mixedWiredFaceBoundaryGraph_le_openFaceDual
        G hn hlt omega))).support,
      z ∈ rlc_pathVertices gamma.1)
    (hleft : ∃ z ∈ (rlc_dualReflectOpenWalk
      (rlc_wiredConnectorConfig gamma gamma'
        (rlc_mixedAxisGapEdges G) omega)
      (c.mapLe (rlc_mixedWiredFaceBoundaryGraph_le_openFaceDual
        G hn hlt omega))).support,
      z ∈ rlc_pathVertices gamma'.1) :
    rlc_dualReflectConfig omega ∈ rlc_mixedWiredConnectorEvent G := by
  obtain ⟨q, _hqEdges, hqSupport⟩ :=
    rlc_dualReflect_wired_faceBoundaryWalk_of_relaxed_region_incident
      G hn hlt omega c hloc
  apply rlc_mixedWiredConnectorEvent_of_openWalk_meets_paths
    G (rlc_dualReflectConfig omega) q
  · simpa [hqSupport] using hbox
  · simpa [hqSupport] using hright
  · simpa [hqSupport] using hleft






theorem rlc_dualReflect_wired_faceBoundaryWalk_of_region_incident {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2))) {x y : Site 2}
    (c : (faceBoundaryGraph
      (rlc_mixedWiredReachSet G omega)).Walk x y)
    (htarget : ∀ {f g : Site 2}, s(f, g) ∈ c.edges →
      s(rlc_dualReflect f, rlc_dualReflect g) ∈
        (rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1) ∪
          rlc_mixedAxisGapEdges G)
    (hloc : ∀ {f g : Site 2}, s(f, g) ∈ c.edges →
      ∃ p q : Site 2,
        sharedPrimalEdge f g = s(p, q) ∧
        p ∈ rect (-2 * n) (2 * n) (-n) n ∧
        q ∈ rect (-2 * n) (2 * n) (-n) n ∧
        (p ∈ rlc_axisGapRegion G ∨ q ∈ rlc_axisGapRegion G)) :
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
  apply rlc_dualReflect_wired_faceBoundaryWalk_of_support
    G hn hlt omega c htarget
  intro f g hfgEdge
  obtain ⟨p, q, hshared, hpR, hqR, hincident⟩ := hloc hfgEdge
  have hsource :=
    rlc_mixedWired_faceBoundary_preimage_mem_mixedSupport_of_region_incident
      G hn hlt omega (c.adj_of_mem_edges hfgEdge)
      hshared hpR hqR hincident
  rw [rlc_pimsEdgeEquiv_reflected_faceBoundaryEdge
    (rlc_mixedWiredReachSet G omega) (c.adj_of_mem_edges hfgEdge)] at hsource
  exact hsource

end Universality
end StatMech
