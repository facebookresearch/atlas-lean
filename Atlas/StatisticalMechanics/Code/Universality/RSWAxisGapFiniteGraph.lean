/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.RSWConnectorFiniteGraph










open Finset SimpleGraph Set

namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section



def rlc_axisGapFiniteGraph {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') :
    SimpleGraph (RlcConnectorVertex n) where
  Adj x y :=
    (hypercubicLattice 2).Adj (x : Site 2) (y : Site 2) ∧
      s((x : Site 2), (y : Site 2)) ∈ rlc_axisGapEdges G
  symm := by
    intro x y hxy
    exact ⟨hxy.1.symm, by simpa [Sym2.eq_swap] using hxy.2⟩
  loopless := ⟨fun x hxx => hxx.1.ne rfl⟩

noncomputable instance rlc_axisGapFiniteGraph_decidableAdj {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') :
    DecidableRel (rlc_axisGapFiniteGraph G).Adj :=
  Classical.decRel _



def rlc_axisGapPlanarDomain {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') :
    Lattice.PlanarZ2Subgraph where
  V := RlcConnectorVertex n
  finV := inferInstance
  decV := inferInstance
  G := rlc_axisGapFiniteGraph G
  emb := ⟨Subtype.val, Subtype.val_injective⟩
  isSub := by
    intro x y hxy
    exact hxy.1



theorem rlc_openSub_axisGapFiniteGraph_restrict_eq {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (omega : ConfigSpace (Sym2 (Site 2))) :
    FK.openSub (rlc_axisGapFiniteGraph G)
        (rlc_connectorRestrictConfig omega) =
      openSubgraphInduce 2
        (rlc_maskConfig (rlc_axisGapEdges G) omega)
        (rect (-2 * n) (2 * n) (-n) n) := by
  ext x y
  rw [FK.openSub_adj, openSubgraphInduce_adj, openSubgraph_adj]
  constructor
  · rintro ⟨⟨hadj, hedge⟩, hopen⟩
    refine ⟨hadj, ?_⟩
    simpa [rlc_maskConfig, hedge, rlc_connectorRestrictConfig,
      Sym2.map_mk] using hopen
  · rintro ⟨hadj, hopen⟩
    have hedge : s((x : Site 2), (y : Site 2)) ∈ rlc_axisGapEdges G := by
      by_contra hedge
      simp [rlc_maskConfig, hedge] at hopen
    refine ⟨⟨hadj, hedge⟩, ?_⟩
    simpa [rlc_maskConfig, hedge, rlc_connectorRestrictConfig,
      Sym2.map_mk] using hopen



def rlc_finiteAxisGapConnectorEvent {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') :
    Set (ConfigSpace (Sym2 (RlcConnectorVertex n))) :=
  {tau | ∃ x y : RlcConnectorVertex n,
    rlc_connectorOnRight gamma x ∧ rlc_connectorOnLeft gamma' y ∧
      (FK.openSub (rlc_axisGapFiniteGraph G) tau).Reachable x y}



theorem rlc_axisGapConnectorEvent_iff_finite {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (omega : ConfigSpace (Sym2 (Site 2))) :
    omega ∈ rlc_axisGapConnectorEvent G ↔
      rlc_connectorRestrictConfig omega ∈
        rlc_finiteAxisGapConnectorEvent G := by
  rw [rlc_axisGapConnectorEvent, rlc_finiteAxisGapConnectorEvent]
  constructor
  · rintro ⟨x, hx, y, hy, hxR, hyR, hxy⟩
    refine ⟨⟨x, hxR⟩, ⟨y, hyR⟩, hx, hy, ?_⟩
    rw [rlc_openSub_axisGapFiniteGraph_restrict_eq]
    exact hxy
  · rintro ⟨x, y, hx, hy, hxy⟩
    refine ⟨x, hx, y, hy, x.2, y.2, ?_⟩
    rw [rlc_openSub_axisGapFiniteGraph_restrict_eq] at hxy
    exact hxy


theorem RlcAxisBarrierGap.lowerVertex_mem_connectorBox {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') :
    G.lowerVertex ∈ rlc_connectorBox n := by
  simpa [rlc_connectorBox] using
    (rlc_rightPathVertex_mem_connectorBox gamma G.lowerVertex_mem_right)


theorem RlcAxisBarrierGap.upperVertex_mem_connectorBox {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') :
    G.upperVertex ∈ rlc_connectorBox n := by
  simpa [rlc_connectorBox] using
    (rlc_leftPathVertex_mem_connectorBox gamma' G.upperVertex_mem_left)



theorem RlcAxisBarrierGap.seedVertex_mem_connectorBox {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') :
    G.seedVertex ∈ rlc_connectorBox n := by
  have hlower := G.lowerVertex_mem_connectorBox
  have hupper := G.upperVertex_mem_connectorBox
  simp only [rlc_connectorBox, Set.Finite.mem_toFinset, mem_rect,
    RlcAxisBarrierGap.lowerVertex, RlcAxisBarrierGap.upperVertex,
    RlcAxisBarrierGap.seedVertex, Matrix.cons_val_zero,
    Matrix.cons_val_one] at hlower hupper ⊢
  have hgap := G.lower_lt_upper
  omega


theorem RlcAxisBarrierGap.firstEdge_mem_axisGapFiniteGraph {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') :
    (rlc_axisGapFiniteGraph G).Adj
      ⟨G.lowerVertex, by
        simpa [rlc_connectorBox] using G.lowerVertex_mem_connectorBox⟩
      ⟨G.seedVertex, by
        simpa [rlc_connectorBox] using G.seedVertex_mem_connectorBox⟩ := by
  constructor
  · simpa [RlcAxisBarrierGap.firstEdge] using G.firstEdge_lattice
  · simp [rlc_axisGapEdges, RlcAxisBarrierGap.firstEdge]



theorem rlc_axisGapEdges_endpoints_mem_connectorBox {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') {v w : Site 2}
    (he : s(v, w) ∈ rlc_axisGapEdges G) :
    v ∈ rlc_connectorBox n ∧ w ∈ rlc_connectorBox n := by
  rw [rlc_axisGapEdges, Finset.mem_union] at he
  rcases he with hinterior | hfirst
  · rw [Finset.mem_filter, mem_edgesWithinFinset] at hinterior
    obtain ⟨⟨x, hx, y, hy, hxy⟩, _⟩ := hinterior
    rw [Sym2.eq_iff] at hxy
    rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨hx, hy⟩
    · exact ⟨hy, hx⟩
  · have heq : s(v, w) = s(G.lowerVertex, G.seedVertex) := by
      simpa [RlcAxisBarrierGap.firstEdge] using hfirst
    rw [Sym2.eq_iff] at heq
    rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨G.lowerVertex_mem_connectorBox,
        G.seedVertex_mem_connectorBox⟩
    · exact ⟨G.seedVertex_mem_connectorBox,
        G.lowerVertex_mem_connectorBox⟩



theorem rlc_axisGapEdge_exists_lift {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') {e : Sym2 (Site 2)}
    (he : e ∈ rlc_axisGapEdges G) :
    ∃ f : Sym2 (RlcConnectorVertex n), f.map Subtype.val = e := by
  induction e using Sym2.inductionOn with
  | _ v w =>
      obtain ⟨hv, hw⟩ :=
        rlc_axisGapEdges_endpoints_mem_connectorBox G he
      let vf : RlcConnectorVertex n := ⟨v, by
        simpa [rlc_connectorBox] using hv⟩
      let wf : RlcConnectorVertex n := ⟨w, by
        simpa [rlc_connectorBox] using hw⟩
      exact ⟨s(vf, wf), by simp [Sym2.map_mk, vf, wf]⟩

noncomputable def rlc_axisGapEdgeLift {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (e : Sym2 (Site 2))
    (he : e ∈ rlc_axisGapEdges G) : Sym2 (RlcConnectorVertex n) :=
  Classical.choose (rlc_axisGapEdge_exists_lift G he)

@[simp] theorem rlc_axisGapEdgeLift_map {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (e : Sym2 (Site 2))
    (he : e ∈ rlc_axisGapEdges G) :
    (rlc_axisGapEdgeLift G e he).map Subtype.val = e :=
  Classical.choose_spec (rlc_axisGapEdge_exists_lift G he)



noncomputable def rlc_axisGapAmbientConfig {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    ConfigSpace (Sym2 (Site 2)) :=
  fun e => if he : e ∈ rlc_axisGapEdges G then
    tau (rlc_axisGapEdgeLift G e he)
  else false

@[simp] theorem rlc_axisGapAmbientConfig_supportEdge {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    {e : Sym2 (Site 2)} (he : e ∈ rlc_axisGapEdges G) :
    rlc_axisGapAmbientConfig G tau e =
      tau (rlc_axisGapEdgeLift G e he) := by
  simp [rlc_axisGapAmbientConfig, he]



theorem rlc_axisGapAmbientConfig_graphEdge {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    {x y : RlcConnectorVertex n}
    (hxy : (rlc_axisGapFiniteGraph G).Adj x y) :
    rlc_connectorRestrictConfig (rlc_axisGapAmbientConfig G tau) s(x, y) =
      tau s(x, y) := by
  have he : s((x : Site 2), (y : Site 2)) ∈ rlc_axisGapEdges G := hxy.2
  rw [rlc_connectorRestrictConfig, Sym2.map_mk,
    rlc_axisGapAmbientConfig_supportEdge G tau he]
  congr 1
  apply Sym2.map.injective Subtype.val_injective
  rw [rlc_axisGapEdgeLift_map]
  rfl



theorem rlc_openSub_restrict_axisGapAmbientConfig_eq {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    FK.openSub (rlc_axisGapFiniteGraph G)
        (rlc_connectorRestrictConfig (rlc_axisGapAmbientConfig G tau)) =
      FK.openSub (rlc_axisGapFiniteGraph G) tau := by
  ext x y
  simp only [FK.openSub_adj]
  constructor
  · rintro ⟨hxy, hopen⟩
    exact ⟨hxy, by
      rw [rlc_axisGapAmbientConfig_graphEdge G tau hxy] at hopen
      exact hopen⟩
  · rintro ⟨hxy, hopen⟩
    exact ⟨hxy, by
      rw [rlc_axisGapAmbientConfig_graphEdge G tau hxy]
      exact hopen⟩



theorem rlc_axisGapAmbientConfig_mem_connectorEvent_iff {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    rlc_axisGapAmbientConfig G tau ∈ rlc_axisGapConnectorEvent G ↔
      tau ∈ rlc_finiteAxisGapConnectorEvent G := by
  rw [rlc_axisGapConnectorEvent_iff_finite]
  unfold rlc_finiteAxisGapConnectorEvent
  simp only [Set.mem_setOf_eq]
  rw [rlc_openSub_restrict_axisGapAmbientConfig_eq]



theorem rlc_finiteAxisGapConnectorFailure_reflectedOpenDualCircuit {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : tau ∉ rlc_finiteAxisGapConnectorEvent G) :
    ∃ (p q f g u : Site 2)
      (c : (openSubgraph 2 (rlc_dualReflectConfig
        (rlc_maskConfig (rlc_axisGapEdges G)
          (rlc_axisGapAmbientConfig G tau)))).Walk
          (rlc_dualReflect u) (rlc_dualReflect u)),
      p 0 = 0 ∧ q 0 = 0 ∧
      sharedPrimalEdge f g = s(p, q) ∧
      c.IsCycle ∧
      s(rlc_dualReflect f, rlc_dualReflect g) ∈ c.edges := by
  apply rlc_axisGapReachSet_reflectedOpenDualCircuit G hn hlt
    (rlc_axisGapAmbientConfig G tau)
  intro hconn
  exact hno ((rlc_axisGapAmbientConfig_mem_connectorEvent_iff G tau).mp hconn)



theorem rlc_axisGapRegionSet_eq_connectorOriginRegionSet_of_origin_mem
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (ho : origin 2 ∈ rlc_axisGapRegionSet G) :
    rlc_axisGapRegionSet G =
      rlc_connectorOriginRegionSet gamma gamma' := by
  ext z
  constructor
  · rintro ⟨hzAllowed, _hseedAllowed, hseedz⟩
    obtain ⟨hoAllowed, _hseedAllowed, hseedOrigin⟩ := ho
    exact ⟨hzAllowed, hoAllowed, hseedOrigin.symm.trans hseedz⟩
  · rintro ⟨hzAllowed, _hoAllowed, horiginz⟩
    obtain ⟨_hoAllowed, hseedAllowed, hseedOrigin⟩ := ho
    exact ⟨hzAllowed, hseedAllowed, hseedOrigin.trans horiginz⟩


theorem rlc_axisGapRegion_eq_connectorOriginRegion_of_origin_mem
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (ho : origin 2 ∈ rlc_axisGapRegionSet G) :
    rlc_axisGapRegion G =
      rlc_connectorOriginRegion gamma gamma' := by
  ext z
  simpa [rlc_axisGapRegion, rlc_connectorOriginRegion] using
    Set.ext_iff.mp
      (rlc_axisGapRegionSet_eq_connectorOriginRegionSet_of_origin_mem G ho) z



theorem rlc_axisGapEdges_eq_connectorEdges_of_origin_mem
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (ho : origin 2 ∈ rlc_axisGapRegionSet G) :
    rlc_axisGapEdges G = rlc_connectorEdges gamma gamma' := by
  have hregion :=
    rlc_axisGapRegion_eq_connectorOriginRegion_of_origin_mem G ho
  obtain ⟨_hoAllowed, hseedAllowed, _hseedOrigin⟩ := ho
  have hseedSet : G.seedVertex ∈ rlc_axisGapRegionSet G :=
    ⟨hseedAllowed, hseedAllowed, SimpleGraph.Reachable.refl _⟩
  have hseed : G.seedVertex ∈ rlc_connectorOriginRegion gamma gamma' := by
    rw [← hregion]
    simpa [rlc_axisGapRegion] using hseedSet
  have hfirst : G.firstEdge ∈ rlc_connectorEdges gamma gamma' := by
    rw [rlc_connectorEdges, Finset.mem_filter]
    constructor
    · rw [mem_edgesWithinFinset]
      exact ⟨G.lowerVertex, G.lowerVertex_mem_connectorBox,
        G.seedVertex, G.seedVertex_mem_connectorBox,
        by simp [RlcAxisBarrierGap.firstEdge]⟩
    · exact ⟨G.seedVertex, hseed, by
        simp [RlcAxisBarrierGap.firstEdge]⟩
  rw [rlc_axisGapEdges, rlc_connectorEdges, hregion]
  apply Finset.union_eq_left.mpr
  simpa [rlc_connectorEdges] using hfirst



theorem rlc_axisGapFiniteGraph_eq_connectorFiniteGraph_of_origin_mem
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (ho : origin 2 ∈ rlc_axisGapRegionSet G) :
    rlc_axisGapFiniteGraph G = rlc_connectorFiniteGraph gamma gamma' := by
  ext x y
  simp only [rlc_axisGapFiniteGraph, rlc_connectorFiniteGraph]
  rw [rlc_axisGapEdges_eq_connectorEdges_of_origin_mem G ho]



theorem rlc_axisGapConnectorEvent_eq_connectorEvent_of_origin_mem
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (ho : origin 2 ∈ rlc_axisGapRegionSet G) :
    rlc_axisGapConnectorEvent G = rlc_connectorEvent gamma gamma' := by
  unfold rlc_axisGapConnectorEvent rlc_connectorEvent
  rw [rlc_axisGapEdges_eq_connectorEdges_of_origin_mem G ho]

end

end StatMech.Universality
