/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Universality.RSWConnectorMassDualityScaleOneAudit
import Code.Universality.RSWAxisGapFiniteGraphRepair











open Finset SimpleGraph Set

namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section


noncomputable def rlc_axisGapAmbientMixedConfig {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    ConfigSpace (Sym2 (Site 2)) :=
  fun e => if he : e ∈ rlc_axisGapEdges G then
    tau (rlc_axisGapEdgeLift G e he)
  else if e ∈ rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1 then true
  else false

@[simp] theorem rlc_axisGapAmbientMixedConfig_supportEdge {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    {e : Sym2 (Site 2)} (he : e ∈ rlc_axisGapEdges G) :
    rlc_axisGapAmbientMixedConfig G tau e =
      tau (rlc_axisGapEdgeLift G e he) := by
  simp [rlc_axisGapAmbientMixedConfig, he]

@[simp] theorem rlc_axisGapAmbientMixedConfig_traceEdge {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    {e : Sym2 (Site 2)}
    (hdisj : Disjoint (rlc_pathVertices gamma.1)
      (rlc_pathVertices gamma'.1))
    (he : e ∈ rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1) :
    rlc_axisGapAmbientMixedConfig G tau e = true := by
  have hnot : e ∉ rlc_axisGapEdges G := by
    rcases Finset.mem_union.mp he with hright | hleft
    · exact Finset.disjoint_left.mp
        (rlc_rightPathEdges_disjoint_axisGapEdges G hdisj) hright
    · exact Finset.disjoint_left.mp
        (rlc_leftPathEdges_disjoint_axisGapEdges G hdisj) hleft
  simp [rlc_axisGapAmbientMixedConfig, hnot, he]

@[simp] theorem rlc_axisGapAmbientMixedConfig_exterior {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    {e : Sym2 (Site 2)} (hG : e ∉ rlc_axisGapEdges G)
    (htrace : e ∉ rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1) :
    rlc_axisGapAmbientMixedConfig G tau e = false := by
  simp [rlc_axisGapAmbientMixedConfig, hG, htrace]


noncomputable def rlc_axisGapPIMSMixedReflectedConfig {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    ConfigSpace (Sym2 (RlcConnectorVertex n)) :=
  rlc_connectorRestrictConfig
    (rlc_dualReflectConfig (rlc_axisGapAmbientMixedConfig G tau))

theorem rlc_axisGapPIMSMixedReflectedConfig_apply {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (e : Sym2 (RlcConnectorVertex n)) :
    rlc_axisGapPIMSMixedReflectedConfig G tau e =
      !(rlc_axisGapAmbientMixedConfig G tau
        (rlc_pimsEdgeEquiv (e.map Subtype.val))) := by
  unfold rlc_axisGapPIMSMixedReflectedConfig rlc_connectorRestrictConfig
  exact rlc_dualReflectConfig_eq_pims
    (rlc_axisGapAmbientMixedConfig G tau) (e.map Subtype.val)


theorem rlc_axisGap_seed_mem_allowed {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper) :
    G.seedVertex ∈ rlc_connectorAllowed gamma gamma' :=
  G.seedVertex_mem_allowed_of_lt hn hlt

theorem rlc_axisGap_seed_not_mem_barrier {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper) :
    G.seedVertex ∉ rlc_connectorBarrier gamma gamma' :=
  (Finset.mem_sdiff.mp (rlc_axisGap_seed_mem_allowed G hn hlt)).2



theorem rlc_axisGapEdges_ne_empty {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') :
    rlc_axisGapEdges G ≠ ∅ := by
  intro hempty
  have hfirst : G.firstEdge ∈ rlc_axisGapEdges G := by
    simp [rlc_axisGapEdges]
  rw [hempty] at hfirst
  simp at hfirst

theorem rlc_axisGapFiniteGraph_ne_bot {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') :
    rlc_axisGapFiniteGraph G ≠ ⊥ := by
  intro hbot
  have hfirst := G.firstEdge_mem_axisGapFiniteGraph
  rw [hbot] at hfirst
  exact hfirst



theorem rlc_axisGapAmbientMixedConfig_eq_connectorAmbient_of_origin_mem
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (ho : origin 2 ∈ rlc_axisGapRegionSet G)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    rlc_axisGapAmbientMixedConfig G tau =
      rlc_connectorAmbientMixedConfig gamma gamma' tau := by
  funext e
  have hedge := rlc_axisGapEdges_eq_connectorEdges_of_origin_mem G ho
  by_cases he : e ∈ rlc_axisGapEdges G
  · have he' : e ∈ rlc_connectorEdges gamma gamma' := by rwa [← hedge]
    rw [rlc_axisGapAmbientMixedConfig_supportEdge G tau he,
      rlc_connectorAmbientMixedConfig_connectorEdge gamma gamma' tau he']
    congr 1
  · have he' : e ∉ rlc_connectorEdges gamma gamma' := by
      rwa [← hedge]
    unfold rlc_axisGapAmbientMixedConfig rlc_connectorAmbientMixedConfig
    simp only [dif_neg he, dif_neg he']

theorem rlc_axisGapPIMSMixed_eq_connectorPIMS_of_origin_mem
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (ho : origin 2 ∈ rlc_axisGapRegionSet G)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    rlc_axisGapPIMSMixedReflectedConfig G tau =
      rlc_connectorPIMSReflectedConfig gamma gamma' tau := by
  unfold rlc_axisGapPIMSMixedReflectedConfig
    rlc_connectorPIMSReflectedConfig
  rw [rlc_axisGapAmbientMixedConfig_eq_connectorAmbient_of_origin_mem
    G ho tau]



theorem rlc_scaleTwo_seededOrdinary_graph_nonempty :
    rlc_axisGapFiniteGraph rlc_scaleTwoDoubleFailureGap ≠ ⊥ :=
  rlc_axisGapFiniteGraph_ne_bot rlc_scaleTwoDoubleFailureGap

private theorem rlc_scaleOne_origin_mem_seededRegion :
    origin 2 ∈ rlc_axisGapRegionSet rlc_windingSideCounterexampleGap := by
  rw [show origin 2 = (![0, 0] : Site 2) by
    ext i
    fin_cases i <;> rfl]
  have h := rlc_windingSideCounterexampleGap.seedVertex_mem_region_of_lt
    (by norm_num) (by norm_num [rlc_windingSideCounterexampleGap])
  simpa [rlc_axisGapRegion, rlc_windingSideCounterexampleGap,
    RlcAxisBarrierGap.seedVertex] using h

private theorem rlc_scaleOne_seeded_finiteEvent_eq :
    rlc_finiteAxisGapConnectorEvent rlc_windingSideCounterexampleGap =
      rlc_finiteConnectorEvent rlc_traceSplitCounterexampleRight
        rlc_traceSplitCounterexampleLeft := by
  unfold rlc_finiteAxisGapConnectorEvent rlc_finiteConnectorEvent
  rw [rlc_axisGapFiniteGraph_eq_connectorFiniteGraph_of_origin_mem
    rlc_windingSideCounterexampleGap rlc_scaleOne_origin_mem_seededRegion]




theorem rlc_scaleOne_seededOrdinary_success_nonempty :
    (rlc_axisGapPIMSMixedReflectedConfig
        rlc_windingSideCounterexampleGap ⁻¹'
      rlc_finiteAxisGapConnectorEvent
        rlc_windingSideCounterexampleGap).Nonempty := by
  refine ⟨rlc_traceSplitCounterexampleFiniteAllClosed, ?_⟩
  change rlc_axisGapPIMSMixedReflectedConfig
      rlc_windingSideCounterexampleGap
        rlc_traceSplitCounterexampleFiniteAllClosed ∈
    rlc_finiteAxisGapConnectorEvent rlc_windingSideCounterexampleGap
  rw [rlc_axisGapPIMSMixed_eq_connectorPIMS_of_origin_mem
    rlc_windingSideCounterexampleGap
    rlc_scaleOne_origin_mem_seededRegion,
    rlc_scaleOne_seeded_finiteEvent_eq]
  exact rlc_traceSplitCounterexample_PIMS_success_via_boundaryArc

end

end StatMech.Universality
