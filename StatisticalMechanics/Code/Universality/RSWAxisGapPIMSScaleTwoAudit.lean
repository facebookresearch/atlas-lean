/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Universality.RSWStoppedPathPIMSProvenance
import Code.Universality.QOneRSWActiveSeed
import Code.Universality.RSWConnectorActualSelectedObstruction











open Finset SimpleGraph Set

namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

def rlc_scaleTwoAxisGapRestrictedConfig :
    ConfigSpace (Sym2 (RlcConnectorVertex 2)) :=
  rlc_connectorRestrictConfig rlc_scaleTwoDoubleFailureConfig



theorem rlc_scaleTwoAxisGapRestrictedConfig_failure :
    rlc_scaleTwoAxisGapRestrictedConfig ∉
      rlc_finiteAxisGapConnectorEvent rlc_scaleTwoDoubleFailureGap := by
  intro hfinite
  have hgap : rlc_scaleTwoDoubleFailureConfig ∈
      rlc_axisGapConnectorEvent rlc_scaleTwoDoubleFailureGap :=
    (rlc_axisGapConnectorEvent_iff_finite
      rlc_scaleTwoDoubleFailureGap rlc_scaleTwoDoubleFailureConfig).mpr
      hfinite
  exact rlc_scaleTwoDoubleFailure_original_failure
    (rlc_mixedAxisGapConnectorEvent_subset_mixedWiredConnectorEvent
      rlc_scaleTwoDoubleFailureGap
      (rq1_axisGapConnectorEvent_subset_mixedAxisGapConnectorEvent
        rlc_scaleTwoDoubleFailureGap
        rlc_scaleTwoDoubleFailure_exposedPaths_disjoint hgap))

private theorem rlc_scaleTwoAxisGap_seed_no_allowed_neighbor
    {v : Site 2}
    (hv : v ∈ rlc_connectorAllowed rlc_scaleTwoDoubleFailureRight
      rlc_scaleTwoDoubleFailureLeft)
    (hadj : (hypercubicLattice 2).Adj (![0, -1] : Site 2) v) : False := by
  have hvCand := mem_candFinset_of_adj 2 (![0, -1] : Site 2) v hadj
  rw [candFinset_face] at hvCand
  simp only [Finset.mem_insert, Finset.mem_singleton] at hvCand
  have hvBarrier := (Finset.mem_sdiff.mp hv).2
  rcases hvCand with rfl | rfl | rfl | rfl <;> apply hvBarrier <;>
    rw [rlc_connectorBarrier,
      rlc_scaleTwoDoubleFailure_right_vertices,
      rlc_scaleTwoDoubleFailure_left_vertices] <;>
    simp [rlc_flipX, rlc_flipXFun]

theorem rlc_scaleTwoAxisGapRegion_eq_singleton :
    rlc_axisGapRegion rlc_scaleTwoDoubleFailureGap =
      {(![0, -1] : Site 2)} := by
  ext z
  constructor
  · intro hz
    have hzSet : z ∈ rlc_axisGapRegionSet
        rlc_scaleTwoDoubleFailureGap := by
      simpa [rlc_axisGapRegion] using hz
    obtain ⟨hzAllowed, _hseedAllowed, hreach⟩ := hzSet
    obtain ⟨w⟩ := hreach
    cases w with
    | nil =>
        simp [rlc_scaleTwoDoubleFailureGap,
          RlcAxisBarrierGap.seedVertex]
    | @cons _ b _ hab _ =>
        rw [SimpleGraph.induce_adj] at hab
        exact False.elim
          (rlc_scaleTwoAxisGap_seed_no_allowed_neighbor b.2 (by
            simpa [rlc_scaleTwoDoubleFailureGap,
              RlcAxisBarrierGap.seedVertex] using hab))
  · intro hz
    simp only [Finset.mem_singleton] at hz
    subst z
    simpa [rlc_scaleTwoDoubleFailureGap,
      RlcAxisBarrierGap.seedVertex] using
      (rlc_scaleTwoDoubleFailureGap.seedVertex_mem_region_of_lt
        (by norm_num) (by norm_num [rlc_scaleTwoDoubleFailureGap]))

theorem rlc_scaleTwoAxisGap_westEdge_mem :
    s((![-1, -1] : Site 2), ![0, -1]) ∈
      rlc_axisGapEdges rlc_scaleTwoDoubleFailureGap := by
  rw [rlc_axisGapEdges, Finset.mem_union]
  left
  rw [Finset.mem_filter]
  exact ⟨by
      rw [mem_edgesWithinFinset]
      exact ⟨![-1, -1], by simp [rlc_connectorBox, mem_rect],
        ![0, -1], by simp [rlc_connectorBox, mem_rect], rfl⟩,
    ⟨![0, -1], by
      rw [rlc_scaleTwoAxisGapRegion_eq_singleton]
      simp, Sym2.mem_mk_right _ _⟩⟩

theorem rlc_scaleTwoAxisGap_leftEdge_mem :
    s((![0, -1] : Site 2), ![0, 0]) ∈
      rlc_axisGapEdges rlc_scaleTwoDoubleFailureGap := by
  rw [rlc_axisGapEdges, Finset.mem_union]
  left
  rw [Finset.mem_filter]
  exact ⟨by
      rw [mem_edgesWithinFinset]
      exact ⟨![0, -1], by simp [rlc_connectorBox, mem_rect],
        ![0, 0], by simp [rlc_connectorBox, mem_rect], rfl⟩,
    ⟨![0, -1], by
      rw [rlc_scaleTwoAxisGapRegion_eq_singleton]
      simp, Sym2.mem_mk_left _ _⟩⟩



def rlc_scaleTwoAxisGapDoubleFailureConfig :
    ConfigSpace (Sym2 (RlcConnectorVertex 2)) :=
  fun e => e.map Subtype.val =
    s((![-1, -1] : Site 2), ![0, -1])

theorem rlc_scaleTwoAxisGap_left_neighbor
    {x y : RlcConnectorVertex 2}
    (hx : rlc_connectorOnLeft rlc_scaleTwoDoubleFailureLeft x)
    (hxy : (rlc_axisGapFiniteGraph
      rlc_scaleTwoDoubleFailureGap).Adj x y) :
    (x : Site 2) = ![0, 0] ∧ (y : Site 2) = ![0, -1] := by
  have hxNotSeed : (x : Site 2) ≠ ![0, -1] := by
    intro hxSeed
    rw [rlc_connectorOnLeft,
      rlc_scaleTwoDoubleFailure_left_vertices] at hx
    simp [hxSeed] at hx
  have hySeed : (y : Site 2) = ![0, -1] := by
    have hsupport : s((x : Site 2), (y : Site 2)) ∈
        rlc_axisGapEdges rlc_scaleTwoDoubleFailureGap := hxy.2
    rw [rlc_axisGapEdges, Finset.mem_union] at hsupport
    rcases hsupport with hinterior | hfirst
    · obtain ⟨_hedge, z, hzRegion, hzEdge⟩ :=
        Finset.mem_filter.mp hinterior
      rw [rlc_scaleTwoAxisGapRegion_eq_singleton] at hzRegion
      simp only [Finset.mem_singleton] at hzRegion
      subst z
      rw [Sym2.mem_iff] at hzEdge
      rcases hzEdge with hzEdge | hzEdge
      · exact False.elim (hxNotSeed hzEdge.symm)
      · exact hzEdge.symm
    · have hedge : s((x : Site 2), (y : Site 2)) =
          s((![0, -2] : Site 2), ![0, -1]) := by
        simpa [rlc_scaleTwoDoubleFailureGap,
          RlcAxisBarrierGap.firstEdge,
          RlcAxisBarrierGap.lowerVertex,
          RlcAxisBarrierGap.seedVertex] using hfirst
      rw [Sym2.eq_iff] at hedge
      rcases hedge with ⟨hxE, _⟩ | ⟨hxC, _⟩
      · rw [rlc_connectorOnLeft,
          rlc_scaleTwoDoubleFailure_left_vertices] at hx
        simp [hxE] at hx
      · exact False.elim (hxNotSeed hxC)
  refine ⟨?_, hySeed⟩
  have hxVertices := hx
  rw [rlc_connectorOnLeft,
    rlc_scaleTwoDoubleFailure_left_vertices] at hxVertices
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxVertices
  have hadj := hxy.1
  rw [hySeed] at hadj
  rcases hxVertices with hxv | hxv | hxv | hxv | hxv | hxv | hxv <;>
    rw [hxv] at hadj ⊢ <;>
    simp [hypercubicLattice_adj, Fin.sum_univ_two] at hadj ⊢



theorem rlc_scaleTwoAxisGap_right_neighbor
    {x y : RlcConnectorVertex 2}
    (hx : rlc_connectorOnRight rlc_scaleTwoDoubleFailureRight x)
    (hxy : (rlc_axisGapFiniteGraph
      rlc_scaleTwoDoubleFailureGap).Adj x y) :
    ((x : Site 2) = ![0, -2] ∨ (x : Site 2) = ![1, -1]) ∧
      (y : Site 2) = ![0, -1] := by
  have hxNotSeed : (x : Site 2) ≠ ![0, -1] := by
    intro hxSeed
    rw [rlc_connectorOnRight,
      rlc_scaleTwoDoubleFailure_right_vertices] at hx
    simp [hxSeed] at hx
  have hySeed : (y : Site 2) = ![0, -1] := by
    have hsupport : s((x : Site 2), (y : Site 2)) ∈
        rlc_axisGapEdges rlc_scaleTwoDoubleFailureGap := hxy.2
    rw [rlc_axisGapEdges, Finset.mem_union] at hsupport
    rcases hsupport with hinterior | hfirst
    · obtain ⟨_hedge, z, hzRegion, hzEdge⟩ :=
        Finset.mem_filter.mp hinterior
      rw [rlc_scaleTwoAxisGapRegion_eq_singleton] at hzRegion
      simp only [Finset.mem_singleton] at hzRegion
      subst z
      rw [Sym2.mem_iff] at hzEdge
      rcases hzEdge with hzEdge | hzEdge
      · exact False.elim (hxNotSeed hzEdge.symm)
      · exact hzEdge.symm
    · have hedge : s((x : Site 2), (y : Site 2)) =
          s((![0, -2] : Site 2), ![0, -1]) := by
        simpa [rlc_scaleTwoDoubleFailureGap,
          RlcAxisBarrierGap.firstEdge,
          RlcAxisBarrierGap.lowerVertex,
          RlcAxisBarrierGap.seedVertex] using hfirst
      rw [Sym2.eq_iff] at hedge
      rcases hedge with ⟨_, hyC⟩ | ⟨hxC, _⟩
      · exact hyC
      · exact False.elim (hxNotSeed hxC)
  refine ⟨?_, hySeed⟩
  have hxVertices := hx
  rw [rlc_connectorOnRight,
    rlc_scaleTwoDoubleFailure_right_vertices] at hxVertices
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxVertices
  have hadj := hxy.1
  rw [hySeed] at hadj
  rcases hxVertices with hxv | hxv | hxv | hxv | hxv | hxv | hxv <;>
    rw [hxv] at hadj ⊢ <;>
    simp [hypercubicLattice_adj, Fin.sum_univ_two] at hadj ⊢

theorem rlc_scaleTwoAxisGap_failure_of_leftEdge_closed
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex 2)))
    (hclosed : rho
      s(⟨![0, -1], by simp [mem_rect]⟩,
        ⟨![0, 0], by simp [mem_rect]⟩) = false) :
    rho ∉ rlc_finiteAxisGapConnectorEvent
      rlc_scaleTwoDoubleFailureGap := by
  rintro ⟨x, y, hx, hy, hreach⟩
  obtain ⟨w⟩ := hreach
  cases w.reverse with
  | nil =>
      exact Finset.disjoint_left.mp
        rlc_scaleTwoDoubleFailure_exposedPaths_disjoint hx hy
  | @cons _ z _ hyz _ =>
      rw [FK.openSub_adj] at hyz
      obtain ⟨hyI, hzC⟩ :=
        rlc_scaleTwoAxisGap_left_neighbor hy hyz.1
      have hedge : s(y, z) =
          s(⟨![0, -1], by simp [mem_rect]⟩,
            ⟨![0, 0], by simp [mem_rect]⟩) := by
        apply Sym2.map.injective Subtype.val_injective
        simp only [Sym2.map_mk]
        rw [hyI, hzC, Sym2.eq_swap]
      rw [hedge, hclosed] at hyz
      simp at hyz

theorem rlc_scaleTwoAxisGapDoubleFailureConfig_failure :
    rlc_scaleTwoAxisGapDoubleFailureConfig ∉
      rlc_finiteAxisGapConnectorEvent rlc_scaleTwoDoubleFailureGap := by
  apply rlc_scaleTwoAxisGap_failure_of_leftEdge_closed
  simp [rlc_scaleTwoAxisGapDoubleFailureConfig, Sym2.map_mk]

private theorem rlc_scaleTwoAxisGapDoubleFailureConfig_PIMS_leftEdge_closed :
    rlc_axisGapPIMSReflectedConfig rlc_scaleTwoDoubleFailureGap
      rlc_scaleTwoAxisGapDoubleFailureConfig
      s(⟨![0, -1], by simp [mem_rect]⟩,
        ⟨![0, 0], by simp [mem_rect]⟩) = false := by
  rw [rlc_axisGapPIMSReflectedConfig_apply]
  have herase :
      (s(⟨![0, -1], by simp [mem_rect]⟩,
        ⟨![0, 0], by simp [mem_rect]⟩) :
          Sym2 (RlcConnectorVertex 2)).map Subtype.val =
        s((![0, -1] : Site 2), ![0, 0]) := by
    rfl
  rw [herase]
  have hpims : rlc_pimsEdgeEquiv
      s((![0, -1] : Site 2), ![0, 0]) =
      s((![-1, -1] : Site 2), ![0, -1]) := by
    simpa using rlc_pimsEdgeEquiv_vertical 0 (-1)
  rw [hpims, rlc_axisGapAmbientConfig_supportEdge
    rlc_scaleTwoDoubleFailureGap rlc_scaleTwoAxisGapDoubleFailureConfig
      rlc_scaleTwoAxisGap_westEdge_mem]
  simp [rlc_scaleTwoAxisGapDoubleFailureConfig,
    rlc_axisGapEdgeLift_map]

theorem rlc_scaleTwoAxisGapDoubleFailureConfig_PIMS_failure :
    rlc_axisGapPIMSReflectedConfig rlc_scaleTwoDoubleFailureGap
        rlc_scaleTwoAxisGapDoubleFailureConfig ∉
      rlc_finiteAxisGapConnectorEvent rlc_scaleTwoDoubleFailureGap :=
  rlc_scaleTwoAxisGap_failure_of_leftEdge_closed _
    rlc_scaleTwoAxisGapDoubleFailureConfig_PIMS_leftEdge_closed



theorem rlc_scaleTwoAxisGap_doubleFailure :
    rlc_scaleTwoAxisGapDoubleFailureConfig ∉
        rlc_finiteAxisGapConnectorEvent rlc_scaleTwoDoubleFailureGap ∧
      rlc_axisGapPIMSReflectedConfig rlc_scaleTwoDoubleFailureGap
          rlc_scaleTwoAxisGapDoubleFailureConfig ∉
        rlc_finiteAxisGapConnectorEvent rlc_scaleTwoDoubleFailureGap :=
  ⟨rlc_scaleTwoAxisGapDoubleFailureConfig_failure,
    rlc_scaleTwoAxisGapDoubleFailureConfig_PIMS_failure⟩



theorem rlc_scaleTwoAxisGap_not_failureSelectedSideTopology :
    ¬ RlcAxisGapPIMSFailureSelectedSideTopology
      rlc_scaleTwoDoubleFailureGap (by norm_num)
        (by norm_num [rlc_scaleTwoDoubleFailureGap]) := by
  intro htopology
  exact rlc_scaleTwoAxisGapDoubleFailureConfig_PIMS_failure
    (rlc_axisGapPIMS_success_of_failureSelectedSideTopology
      rlc_scaleTwoDoubleFailureGap (by norm_num)
      (by norm_num [rlc_scaleTwoDoubleFailureGap]) htopology
      rlc_scaleTwoAxisGapDoubleFailureConfig
      rlc_scaleTwoAxisGapDoubleFailureConfig_failure)

end

end StatMech.Universality
