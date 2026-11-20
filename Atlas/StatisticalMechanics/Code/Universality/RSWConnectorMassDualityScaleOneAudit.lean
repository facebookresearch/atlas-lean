/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Universality.RSWConnectorMassDualityCapstone
import Code.Universality.RSWStoppedPathPIMSActiveObstruction











open Finset SimpleGraph Set

namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

private theorem rlc_scaleOne_origin_eq :
    origin 2 = (![0, 0] : Site 2) := by
  ext i
  fin_cases i <;> rfl

theorem rlc_scaleOne_origin_mem_gapRegionSet :
    origin 2 ∈ rlc_axisGapRegionSet rlc_windingSideCounterexampleGap := by
  rw [rlc_scaleOne_origin_eq]
  have h := rlc_windingSideCounterexampleGap.seedVertex_mem_region_of_lt
    (by norm_num) (by norm_num [rlc_windingSideCounterexampleGap])
  simpa [rlc_axisGapRegion, rlc_windingSideCounterexampleGap,
    RlcAxisBarrierGap.seedVertex] using h

private theorem rlc_scaleOne_graph_eq :
    rlc_axisGapFiniteGraph rlc_windingSideCounterexampleGap =
      rlc_connectorFiniteGraph rlc_traceSplitCounterexampleRight
        rlc_traceSplitCounterexampleLeft :=
  rlc_axisGapFiniteGraph_eq_connectorFiniteGraph_of_origin_mem
    rlc_windingSideCounterexampleGap rlc_scaleOne_origin_mem_gapRegionSet

private theorem rlc_scaleOne_finiteEvent_eq :
    rlc_finiteAxisGapConnectorEvent rlc_windingSideCounterexampleGap =
      rlc_finiteConnectorEvent rlc_traceSplitCounterexampleRight
        rlc_traceSplitCounterexampleLeft := by
  unfold rlc_finiteAxisGapConnectorEvent rlc_finiteConnectorEvent
  rw [rlc_scaleOne_graph_eq]

private theorem rlc_scaleOne_axisAmbient_le_mixedAmbient
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex 1))) :
    rlc_axisGapAmbientConfig rlc_windingSideCounterexampleGap tau ≤
      rlc_connectorAmbientMixedConfig rlc_traceSplitCounterexampleRight
        rlc_traceSplitCounterexampleLeft tau := by
  intro e
  have hedge := rlc_axisGapEdges_eq_connectorEdges_of_origin_mem
    rlc_windingSideCounterexampleGap rlc_scaleOne_origin_mem_gapRegionSet
  by_cases he : e ∈ rlc_axisGapEdges rlc_windingSideCounterexampleGap
  · have he' : e ∈ rlc_connectorEdges rlc_traceSplitCounterexampleRight
        rlc_traceSplitCounterexampleLeft := by
      rwa [← hedge]
    rw [rlc_axisGapAmbientConfig_supportEdge
      rlc_windingSideCounterexampleGap tau he,
      rlc_connectorAmbientMixedConfig_connectorEdge
        rlc_traceSplitCounterexampleRight rlc_traceSplitCounterexampleLeft
        tau he']
    have hlift : rlc_axisGapEdgeLift rlc_windingSideCounterexampleGap e he =
        rlc_connectorEdgeLift rlc_traceSplitCounterexampleRight
          rlc_traceSplitCounterexampleLeft e he' := by
      apply Sym2.map.injective Subtype.val_injective
      rw [rlc_axisGapEdgeLift_map, rlc_connectorEdgeLift_map]
    rw [hlift]
  · rw [rlc_axisGapAmbientConfig]
    simp only [dif_neg he]
    exact Bool.false_le _

private theorem rlc_scaleOne_mixedPIMS_le_axisPIMS
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex 1))) :
    rlc_connectorPIMSReflectedConfig rlc_traceSplitCounterexampleRight
        rlc_traceSplitCounterexampleLeft tau ≤
      rlc_axisGapPIMSReflectedConfig
        rlc_windingSideCounterexampleGap tau := by
  intro e
  rw [rlc_connectorPIMSReflectedConfig_apply,
    rlc_axisGapPIMSReflectedConfig_apply]
  have hle := rlc_scaleOne_axisAmbient_le_mixedAmbient tau
    (rlc_pimsEdgeEquiv (e.map Subtype.val))
  cases haxis : rlc_axisGapAmbientConfig
      rlc_windingSideCounterexampleGap tau
      (rlc_pimsEdgeEquiv (e.map Subtype.val)) <;>
    cases hmixed : rlc_connectorAmbientMixedConfig
      rlc_traceSplitCounterexampleRight rlc_traceSplitCounterexampleLeft tau
      (rlc_pimsEdgeEquiv (e.map Subtype.val)) <;>
    simp_all



theorem rlc_activeFullConnector_doubleFailure :
    rlc_activeGapDoubleFailureConfig ∉
        rlc_finiteConnectorEvent rlc_traceSplitCounterexampleRight
          rlc_traceSplitCounterexampleLeft ∧
      rlc_connectorPIMSReflectedConfig rlc_traceSplitCounterexampleRight
          rlc_traceSplitCounterexampleLeft
          rlc_activeGapDoubleFailureConfig ∉
        rlc_finiteConnectorEvent rlc_traceSplitCounterexampleRight
          rlc_traceSplitCounterexampleLeft := by
  constructor
  · rw [← rlc_scaleOne_finiteEvent_eq]
    exact rlc_activeGapDoubleFailureConfig_failure
  · intro hsuccess
    have haxis : rlc_axisGapPIMSReflectedConfig
        rlc_windingSideCounterexampleGap rlc_activeGapDoubleFailureConfig ∈
          rlc_finiteAxisGapConnectorEvent
            rlc_windingSideCounterexampleGap := by
      rw [rlc_scaleOne_finiteEvent_eq]
      exact rlc_finiteConnectorEvent_isIncreasing
        rlc_traceSplitCounterexampleRight rlc_traceSplitCounterexampleLeft
        (rlc_scaleOne_mixedPIMS_le_axisPIMS
          rlc_activeGapDoubleFailureConfig) hsuccess
    exact rlc_activeGapDoubleFailureConfig_PIMS_failure haxis

private theorem rlc_scaleOne_region_cases {z : Site 2}
    (hz : z ∈ rlc_connectorOriginRegion
      rlc_traceSplitCounterexampleRight rlc_traceSplitCounterexampleLeft) :
    z = ![-1, 0] ∨ z = ![0, 0] ∨ z = ![1, 0] := by
  have hzSet : z ∈ rlc_connectorOriginRegionSet
      rlc_traceSplitCounterexampleRight rlc_traceSplitCounterexampleLeft := by
    simpa [rlc_connectorOriginRegion] using hz
  obtain ⟨hzAllowed, _ho, _hreach⟩ := hzSet
  have hzBox := (Finset.mem_sdiff.mp hzAllowed).1
  have hzNotBarrier := (Finset.mem_sdiff.mp hzAllowed).2
  rw [rlc_connectorBox, Set.Finite.mem_toFinset, mem_rect] at hzBox
  rw [rlc_connectorBarrier] at hzNotBarrier
  simp only [Finset.mem_union, not_or] at hzNotBarrier
  rw [rlc_traceSplitCounterexample_right_vertices,
    rlc_traceSplitCounterexample_left_vertices] at hzNotBarrier
  simp [rlc_flipX, rlc_flipXFun] at hzNotBarrier
  have hx : z 0 = -2 ∨ z 0 = -1 ∨ z 0 = 0 ∨ z 0 = 1 ∨ z 0 = 2 := by
    omega
  have hy : z 1 = -1 ∨ z 1 = 0 ∨ z 1 = 1 := by
    omega
  rcases hx with hx | hx | hx | hx | hx <;>
    rcases hy with hy | hy | hy
  all_goals
    have hzEq : z = ![z 0, z 1] := by
      ext i
      fin_cases i <;> simp
    rw [hzEq, hx, hy] at hzNotBarrier ⊢
    try simp at hzNotBarrier ⊢

private theorem rlc_scaleOne_right_neighbor
    {x y : RlcConnectorVertex 1}
    (hx : rlc_connectorOnRight rlc_traceSplitCounterexampleRight x)
    (hxy : (rlc_connectorFiniteGraph rlc_traceSplitCounterexampleRight
      rlc_traceSplitCounterexampleLeft).Adj x y) :
    ((x : Site 2) = ![0, -1] ∧ (y : Site 2) = ![0, 0]) ∨
      ((x : Site 2) = ![1, -1] ∧ (y : Site 2) = ![1, 0]) ∨
      ((x : Site 2) = ![2, 0] ∧ (y : Site 2) = ![1, 0]) := by
  have hxBarrier : (x : Site 2) ∈ rlc_connectorBarrier
      rlc_traceSplitCounterexampleRight rlc_traceSplitCounterexampleLeft := by
    rw [rlc_connectorBarrier]
    simp only [Finset.mem_union]
    exact Or.inl (Or.inl (Or.inl hx))
  have hxNotRegion : (x : Site 2) ∉ rlc_connectorOriginRegion
      rlc_traceSplitCounterexampleRight rlc_traceSplitCounterexampleLeft :=
    fun hxRegion => rlc_originRegion_not_barrier hxRegion hxBarrier
  have hyRegion : (y : Site 2) ∈ rlc_connectorOriginRegion
      rlc_traceSplitCounterexampleRight rlc_traceSplitCounterexampleLeft := by
    obtain ⟨z, hzRegion, hzEdge⟩ :=
      (Finset.mem_filter.mp hxy.2).2
    rw [Sym2.mem_iff] at hzEdge
    rcases hzEdge with hzEdge | hzEdge
    · exact False.elim (hxNotRegion (hzEdge ▸ hzRegion))
    · simpa [hzEdge] using hzRegion
  have hyCases := rlc_scaleOne_region_cases hyRegion
  have hxVertices := hx
  rw [rlc_connectorOnRight,
    rlc_traceSplitCounterexample_right_vertices] at hxVertices
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxVertices
  have hadj := hxy.1
  rcases hxVertices with hxv | hxv | hxv | hxv <;>
    rcases hyCases with hyv | hyv | hyv <;>
    rw [hxv, hyv] at hadj ⊢ <;>
    simp [hypercubicLattice_adj, Fin.sum_univ_two] at hadj ⊢

private theorem rlc_scaleOne_source_not_connector
    {e : Sym2 (Site 2)}
    (hall : forall z, z ∈ e ->
      z ∈ rlc_connectorBarrier rlc_traceSplitCounterexampleRight
        rlc_traceSplitCounterexampleLeft) :
    e ∉ rlc_connectorEdges rlc_traceSplitCounterexampleRight
      rlc_traceSplitCounterexampleLeft := by
  intro he
  obtain ⟨z, hzRegion, hze⟩ := (Finset.mem_filter.mp he).2
  exact rlc_originRegion_not_barrier hzRegion (hall z hze)

private theorem rlc_scaleOne_collared_right_edge_closed
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex 1)))
    {x y : RlcConnectorVertex 1}
    (hx : rlc_connectorOnRight rlc_traceSplitCounterexampleRight x)
    (hxy : (rlc_connectorFiniteGraph rlc_traceSplitCounterexampleRight
      rlc_traceSplitCounterexampleLeft).Adj x y) :
    rlc_connectorPIMSCollaredReflectedConfig
      rlc_traceSplitCounterexampleRight rlc_traceSplitCounterexampleLeft tau
      s(x, y) = false := by
  rcases rlc_scaleOne_right_neighbor hx hxy with
      ⟨hx0, hy0⟩ | ⟨⟨hx1, hy1⟩ | ⟨hx2, hy2⟩⟩
  · have hpre :=
      rlc_traceSplitCounterexample_PIMS_firstEdge_source_exterior
    apply rlc_connectorPIMSCollaredReflectedConfig_of_preimage_exterior
      rlc_traceSplitCounterexampleRight rlc_traceSplitCounterexampleLeft
      tau s(x, y) hxy.2
    · simpa [hx0, hy0, Sym2.map_mk] using hpre.1
    · simpa [hx0, hy0, Sym2.map_mk] using hpre.2
  · have hpims : rlc_pimsEdgeEquiv
        (s(x, y).map Subtype.val) =
          s((![-2, -1] : Site 2), ![-1, -1]) := by
      simpa [hx1, hy1, Sym2.map_mk] using
        rlc_pimsEdgeEquiv_vertical 1 (-1)
    apply rlc_connectorPIMSCollaredReflectedConfig_of_preimage_exterior
      rlc_traceSplitCounterexampleRight rlc_traceSplitCounterexampleLeft
      tau s(x, y) hxy.2
    · rw [hpims]
      apply rlc_scaleOne_source_not_connector
      intro z hz
      rw [Sym2.mem_iff] at hz
      rcases hz with rfl | rfl <;>
        rw [rlc_connectorBarrier,
          rlc_traceSplitCounterexample_right_vertices] <;>
        simp [rlc_flipX, rlc_flipXFun]
    · rw [hpims]
      intro he
      rcases Finset.mem_union.mp he with hright | hleft
      · have hends := rlc_pathEdge_endpoints_mem_vertices
          rlc_traceSplitCounterexampleRight.1 hright
        rw [rlc_traceSplitCounterexample_right_vertices] at hends
        simp at hends
      · have hends := rlc_pathEdge_endpoints_mem_vertices
          rlc_traceSplitCounterexampleLeft.1 hleft
        rw [rlc_traceSplitCounterexample_left_vertices] at hends
        simp at hends
  · have hpims : rlc_pimsEdgeEquiv
        (s(x, y).map Subtype.val) =
          s((![-2, -1] : Site 2), ![-2, 0]) := by
      simpa [hx2, hy2, Sym2.map_mk, Sym2.eq_swap] using
        rlc_pimsEdgeEquiv_horizontal 1 0
    apply rlc_connectorPIMSCollaredReflectedConfig_of_preimage_exterior
      rlc_traceSplitCounterexampleRight rlc_traceSplitCounterexampleLeft
      tau s(x, y) hxy.2
    · rw [hpims]
      apply rlc_scaleOne_source_not_connector
      intro z hz
      rw [Sym2.mem_iff] at hz
      rcases hz with rfl | rfl
      · rw [rlc_connectorBarrier,
          rlc_traceSplitCounterexample_right_vertices]
        simp [rlc_flipX, rlc_flipXFun]
      · rw [rlc_connectorBarrier,
          rlc_traceSplitCounterexample_left_vertices]
        simp
    · rw [hpims]
      intro he
      rcases Finset.mem_union.mp he with hright | hleft
      · have hends := rlc_pathEdge_endpoints_mem_vertices
          rlc_traceSplitCounterexampleRight.1 hright
        rw [rlc_traceSplitCounterexample_right_vertices] at hends
        simp at hends
      · have hends := rlc_pathEdge_endpoints_mem_vertices
          rlc_traceSplitCounterexampleLeft.1 hleft
        rw [rlc_traceSplitCounterexample_left_vertices] at hends
        simp at hends



theorem rlc_traceSplitCounterexample_PIMSCollared_failure
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex 1))) :
    rlc_connectorPIMSCollaredReflectedConfig
        rlc_traceSplitCounterexampleRight rlc_traceSplitCounterexampleLeft tau ∉
      rlc_finiteConnectorEvent rlc_traceSplitCounterexampleRight
        rlc_traceSplitCounterexampleLeft := by
  intro hconn
  obtain ⟨x, y, hx, hy, hxy⟩ := hconn
  obtain ⟨w⟩ := hxy
  cases w with
  | nil =>
      have hdisj : Disjoint
          (rlc_pathVertices rlc_traceSplitCounterexampleRight.1)
          (rlc_pathVertices rlc_traceSplitCounterexampleLeft.1) := by
        rw [Finset.disjoint_left,
          rlc_traceSplitCounterexample_right_vertices,
          rlc_traceSplitCounterexample_left_vertices]
        simp
      exact Finset.disjoint_left.mp hdisj hx hy
  | @cons _ z _ hxz _ =>
      rw [FK.openSub_adj] at hxz
      have hclosed := rlc_scaleOne_collared_right_edge_closed
        tau hx hxz.1
      rw [hclosed] at hxz
      simp at hxz

theorem rlc_traceSplitCounterexample_PIMSCollared_preimage_eq_empty :
    rlc_connectorPIMSCollaredReflectedConfig
        rlc_traceSplitCounterexampleRight rlc_traceSplitCounterexampleLeft ⁻¹'
      rlc_finiteConnectorEvent rlc_traceSplitCounterexampleRight
        rlc_traceSplitCounterexampleLeft = ∅ := by
  ext tau
  simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
  exact rlc_traceSplitCounterexample_PIMSCollared_failure tau

private theorem rlc_scaleOne_forcedDualProb_pos
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex 1))) :
    0 < rlc_connectorForcedDualProb rlc_traceSplitCounterexampleRight
      rlc_traceSplitCounterexampleLeft p q tau := by
  unfold rlc_connectorForcedDualProb
  exact div_pos
    (BeffaraDC.pfd_dualWeight_pos
      (rlc_connectorAugmentedPlanarDomain
        rlc_traceSplitCounterexampleRight rlc_traceSplitCounterexampleLeft)
      (FK.openSub
        (rlc_connectorAugmentedPlanarDomain
          rlc_traceSplitCounterexampleRight
          rlc_traceSplitCounterexampleLeft).G
        (rlc_connectorForceTraceConfig
          rlc_traceSplitCounterexampleRight
          rlc_traceSplitCounterexampleLeft tau)) hp hp1 hq)
    (rlc_connectorForcedDualZ_pos rlc_traceSplitCounterexampleRight
      rlc_traceSplitCounterexampleLeft hp hp1 hq)

private theorem rlc_scaleOne_failure_forcedDualMass_pos
    {q : Real} (hq : 1 <= q) :
    0 < rlc_connectorForcedDualEventMass
      rlc_traceSplitCounterexampleRight rlc_traceSplitCounterexampleLeft
      (BeffaraDC.selfDualPoint q) q
      (rlc_finiteConnectorEvent rlc_traceSplitCounterexampleRight
        rlc_traceSplitCounterexampleLeft)ᶜ := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  obtain ⟨hp, hp1⟩ := BeffaraDC.selfDualPoint_mem_Ioo hq0
  unfold rlc_connectorForcedDualEventMass
  apply Finset.sum_pos'
  · intro tau _
    exact mul_nonneg
      (Set.indicator_nonneg (fun _ _ => zero_le_one) tau)
      (rlc_connectorForcedDualProb_nonneg
        rlc_traceSplitCounterexampleRight rlc_traceSplitCounterexampleLeft
        hp hp1 hq0 tau)
  · refine ⟨rlc_traceSplitCounterexampleFiniteAllClosed,
      Finset.mem_univ _, ?_⟩
    rw [Set.indicator_of_mem (by
      simpa using rlc_traceSplitCounterexample_finiteAllClosed_failure), one_mul]
    exact rlc_scaleOne_forcedDualProb_pos hp hp1 hq0 _




theorem rlc_traceSplitCounterexample_not_PIMSCollaredFailureMassTransport
    {q : Real} (hq : 1 <= q) :
    ¬ RlcConnectorPIMSCollaredFailureMassTransport
      rlc_traceSplitCounterexampleRight rlc_traceSplitCounterexampleLeft q := by
  intro htransport
  unfold RlcConnectorPIMSCollaredFailureMassTransport at htransport
  rw [rlc_traceSplitCounterexample_PIMSCollared_preimage_eq_empty]
    at htransport
  have hempty : rlc_connectorForcedDualEventMass
      rlc_traceSplitCounterexampleRight rlc_traceSplitCounterexampleLeft
      (BeffaraDC.selfDualPoint q) q ∅ = 0 := by
    unfold rlc_connectorForcedDualEventMass
    simp
  rw [hempty] at htransport
  exact (not_lt_of_ge htransport)
    (rlc_scaleOne_failure_forcedDualMass_pos hq)

end

end StatMech.Universality
