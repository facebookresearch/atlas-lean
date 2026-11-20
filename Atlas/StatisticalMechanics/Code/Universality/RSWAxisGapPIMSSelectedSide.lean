/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Universality.RSWAxisGapFiniteGraph










open Finset SimpleGraph Set

namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section



noncomputable def rlc_axisGapPIMSReflectedConfig {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    ConfigSpace (Sym2 (RlcConnectorVertex n)) :=
  rlc_connectorRestrictConfig
    (rlc_dualReflectConfig (rlc_axisGapAmbientConfig G tau))

theorem rlc_maskConfig_axisGapAmbientConfig {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    rlc_maskConfig (rlc_axisGapEdges G) (rlc_axisGapAmbientConfig G tau) =
      rlc_axisGapAmbientConfig G tau := by
  funext e
  by_cases he : e ∈ rlc_axisGapEdges G <;>
    simp [rlc_maskConfig, rlc_axisGapAmbientConfig, he]

theorem rlc_axisGapPIMSReflectedConfig_apply {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (f : Sym2 (RlcConnectorVertex n)) :
    rlc_axisGapPIMSReflectedConfig G tau f =
      !(rlc_axisGapAmbientConfig G tau
        (rlc_pimsEdgeEquiv (f.map Subtype.val))) := by
  unfold rlc_axisGapPIMSReflectedConfig rlc_connectorRestrictConfig
  rw [rlc_dualReflectConfig_eq_pims]




def RlcAxisGapPIMSSourceOpenCase {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (e : Sym2 (Site 2)) : Prop :=
  (∃ hsource : rlc_pimsEdgeEquiv e ∈ rlc_axisGapEdges G,
      tau (rlc_axisGapEdgeLift G (rlc_pimsEdgeEquiv e) hsource) = false) ∨
    rlc_pimsEdgeEquiv e ∉ rlc_axisGapEdges G



theorem rlc_axisGapPIMSSourceOpenCase_of_maskedDual_open {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (e : Sym2 (Site 2))
    (hopen : rlc_dualReflectConfig
      (rlc_maskConfig (rlc_axisGapEdges G)
        (rlc_axisGapAmbientConfig G tau)) e = true) :
    RlcAxisGapPIMSSourceOpenCase G tau e := by
  rw [rlc_maskConfig_axisGapAmbientConfig,
    rlc_dualReflectConfig_eq_pims] at hopen
  by_cases hsource : rlc_pimsEdgeEquiv e ∈ rlc_axisGapEdges G
  · left
    refine ⟨hsource, ?_⟩
    simpa [rlc_axisGapAmbientConfig, hsource] using hopen
  · exact Or.inr hsource



theorem rlc_axisGapPIMSReflectedConfig_open_of_sourceOpenCase {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (e : Sym2 (Site 2)) (htarget : e ∈ rlc_axisGapEdges G)
    (hcase : RlcAxisGapPIMSSourceOpenCase G tau e) :
    rlc_axisGapPIMSReflectedConfig G tau
      (rlc_axisGapEdgeLift G e htarget) = true := by
  rw [rlc_axisGapPIMSReflectedConfig_apply,
    rlc_axisGapEdgeLift_map]
  rcases hcase with ⟨hsource, hclosed⟩ | hsource
  · rw [rlc_axisGapAmbientConfig_supportEdge G tau hsource, hclosed]
    rfl
  · simp [rlc_axisGapAmbientConfig, hsource]


theorem rlc_axisGapPIMSReflectedConfig_open_of_finite_sourceOpenCase
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (e : Sym2 (RlcConnectorVertex n))
    (hcase : RlcAxisGapPIMSSourceOpenCase G tau (e.map Subtype.val)) :
    rlc_axisGapPIMSReflectedConfig G tau e = true := by
  rw [rlc_axisGapPIMSReflectedConfig_apply]
  rcases hcase with ⟨hsource, hclosed⟩ | hsource
  · rw [rlc_axisGapAmbientConfig_supportEdge G tau hsource, hclosed]
    rfl
  · simp [rlc_axisGapAmbientConfig, hsource]



def RlcAxisGapPIMSBoundaryArc {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) : Prop :=
  ∃ (x y : Site 2)
    (a : (faceBoundaryGraph
      (rlc_axisGapReachSet G (rlc_axisGapAmbientConfig G tau))).Walk x y),
    rlc_dualReflect x ∈ rlc_pathVertices gamma.1 ∧
      rlc_dualReflect y ∈ rlc_pathVertices gamma'.1 ∧
      let eta := rlc_maskConfig (rlc_axisGapEdges G)
        (rlc_axisGapAmbientConfig G tau)
      let hle := rlc_axisGapFaceBoundaryGraph_le_openFaceDual
        G hn hlt (rlc_axisGapAmbientConfig G tau)
      ∀ e ∈ (rlc_dualReflectOpenWalk eta (a.mapLe hle)).edges,
        e ∈ rlc_axisGapEdges G


def rlc_axisGapPIMSSelectedSideEvent {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper) :
    Set (ConfigSpace (Sym2 (RlcConnectorVertex n))) :=
  {tau | RlcAxisGapPIMSBoundaryArc G hn hlt tau}



def RlcAxisGapPIMSActualSelectedArc {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) : Prop :=
  ∃ (x y : Site 2)
    (c : (openSubgraph 2 (rlc_dualReflectConfig
      (rlc_maskConfig (rlc_axisGapEdges G)
        (rlc_axisGapAmbientConfig G tau)))).Walk x y),
    x ∈ rlc_pathVertices gamma.1 ∧
      y ∈ rlc_pathVertices gamma'.1 ∧
      (∀ z ∈ c.support,
        z ∈ (rect (-2 * n) (2 * n) (-n) n : Set (Site 2))) ∧
      (∀ e ∈ c.edges, e ∈ rlc_axisGapEdges G) ∧
      ∀ e ∈ c.edges, RlcAxisGapPIMSSourceOpenCase G tau e

theorem rlc_axisGapEdge_endpoint_mem_box {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') {e : Sym2 (Site 2)}
    (he : e ∈ rlc_axisGapEdges G) {z : Site 2} (hz : z ∈ e) :
    z ∈ (rect (-2 * n) (2 * n) (-n) n : Set (Site 2)) := by
  induction e using Sym2.inductionOn with
  | _ v w =>
      obtain ⟨hv, hw⟩ :=
        rlc_axisGapEdges_endpoints_mem_connectorBox G he
      rw [Sym2.mem_iff] at hz
      rcases hz with rfl | rfl
      · simpa [rlc_connectorBox] using hv
      · simpa [rlc_connectorBox] using hw



theorem rlc_walk_support_mem_connectorBox_of_axisGapEdges {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    {H : SimpleGraph (Site 2)} {x y : Site 2} (a : H.Walk x y)
    (hy : y ∈ (rect (-2 * n) (2 * n) (-n) n : Set (Site 2)))
    (hedges : ∀ e ∈ a.edges, e ∈ rlc_axisGapEdges G) :
    ∀ z ∈ a.support,
      z ∈ (rect (-2 * n) (2 * n) (-n) n : Set (Site 2)) := by
  intro z hz
  rw [SimpleGraph.Walk.mem_support_iff_exists_mem_edges] at hz
  rcases hz with rfl | ⟨e, he, hze⟩
  · exact hy
  · exact rlc_axisGapEdge_endpoint_mem_box G (hedges e he) hze



theorem rlc_axisGapPIMSActualSelectedArc_of_boundaryArc {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (harc : RlcAxisGapPIMSBoundaryArc G hn hlt tau) :
    RlcAxisGapPIMSActualSelectedArc G tau := by
  obtain ⟨x, y, a, hx, hy, htarget⟩ := harc
  let eta := rlc_maskConfig (rlc_axisGapEdges G)
    (rlc_axisGapAmbientConfig G tau)
  let hle := rlc_axisGapFaceBoundaryGraph_le_openFaceDual
    G hn hlt (rlc_axisGapAmbientConfig G tau)
  let c := rlc_dualReflectOpenWalk eta (a.mapLe hle)
  have hyBox : rlc_dualReflect y ∈
      (rect (-2 * n) (2 * n) (-n) n : Set (Site 2)) :=
    rlc_leftPathVertex_mem_connectorBox gamma' hy
  refine ⟨rlc_dualReflect x, rlc_dualReflect y, c, hx, hy, ?_,
    htarget, ?_⟩
  · exact rlc_walk_support_mem_connectorBox_of_axisGapEdges
      G c hyBox htarget
  · intro e he
    induction e using Sym2.inductionOn with
    | _ u v =>
        exact rlc_axisGapPIMSSourceOpenCase_of_maskedDual_open
          G tau s(u, v) (c.adj_of_mem_edges he).2



theorem rlc_axisGapPIMS_openWalk_of_actualSelectedArc {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    {x y : Site 2}
    (c : (openSubgraph 2 (rlc_dualReflectConfig
      (rlc_maskConfig (rlc_axisGapEdges G)
        (rlc_axisGapAmbientConfig G tau)))).Walk x y)
    (hsupport : ∀ z ∈ c.support,
      z ∈ (rect (-2 * n) (2 * n) (-n) n : Set (Site 2)))
    (htarget : ∀ e ∈ c.edges, e ∈ rlc_axisGapEdges G)
    (hsource : ∀ e ∈ c.edges, RlcAxisGapPIMSSourceOpenCase G tau e) :
    Nonempty ((FK.openSub (rlc_axisGapFiniteGraph G)
      (rlc_axisGapPIMSReflectedConfig G tau)).Walk
        ⟨x, hsupport x c.start_mem_support⟩
        ⟨y, hsupport y c.end_mem_support⟩) := by
  let cbox := c.induce
    (rect (-2 * n) (2 * n) (-n) n : Set (Site 2)) hsupport
  refine ⟨cbox.transfer
    (FK.openSub (rlc_axisGapFiniteGraph G)
      (rlc_axisGapPIMSReflectedConfig G tau)) ?_⟩
  intro e he
  induction e using Sym2.inductionOn with
  | _ u v =>
      let hom := (SimpleGraph.Embedding.induce
        (G := openSubgraph 2 (rlc_dualReflectConfig
          (rlc_maskConfig (rlc_axisGapEdges G)
            (rlc_axisGapAmbientConfig G tau))))
        (rect (-2 * n) (2 * n) (-n) n : Set (Site 2))).toHom
      have hec : s((u : Site 2), (v : Site 2)) ∈ c.edges := by
        have hmap : s((u : Site 2), (v : Site 2)) ∈
            List.map (Sym2.map hom) cbox.edges :=
          List.mem_map.mpr ⟨s(u, v), he, by rfl⟩
        rw [← SimpleGraph.Walk.edges_map hom cbox] at hmap
        simpa [hom, cbox] using hmap
      have hadj := c.adj_of_mem_edges hec
      rw [SimpleGraph.mem_edgeSet, FK.openSub_adj]
      refine ⟨⟨hadj.1, htarget _ hec⟩, ?_⟩
      exact rlc_axisGapPIMSReflectedConfig_open_of_finite_sourceOpenCase
        G tau s(u, v) (by simpa [Sym2.map_mk] using hsource _ hec)



theorem rlc_axisGapPIMSReflectedConfig_mem_event_of_actualSelectedArc
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (harc : RlcAxisGapPIMSActualSelectedArc G tau) :
    rlc_axisGapPIMSReflectedConfig G tau ∈
      rlc_finiteAxisGapConnectorEvent G := by
  obtain ⟨x, y, c, hx, hy, hsupp, htarget, hsource⟩ := harc
  obtain ⟨cfinite⟩ := rlc_axisGapPIMS_openWalk_of_actualSelectedArc
    G tau c hsupp htarget hsource
  exact ⟨⟨x, hsupp x c.start_mem_support⟩,
    ⟨y, hsupp y c.end_mem_support⟩, hx, hy, ⟨cfinite⟩⟩



theorem rlc_axisGapPIMSReflectedConfig_mem_event_of_boundaryArc
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (harc : RlcAxisGapPIMSBoundaryArc G hn hlt tau) :
    rlc_axisGapPIMSReflectedConfig G tau ∈
      rlc_finiteAxisGapConnectorEvent G :=
  rlc_axisGapPIMSReflectedConfig_mem_event_of_actualSelectedArc G tau
    (rlc_axisGapPIMSActualSelectedArc_of_boundaryArc G hn hlt tau harc)

end

end StatMech.Universality
