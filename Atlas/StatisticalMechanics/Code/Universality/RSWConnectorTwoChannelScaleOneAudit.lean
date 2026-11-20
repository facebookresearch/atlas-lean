/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Universality.RSWConnectorTwoChannel
import Code.Universality.RSWConnectorCentralFaceScaleOneAudit
import Code.Universality.RSWConnectorMassDualityScaleOneAudit











open Finset SimpleGraph Set

namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

private theorem rlc_activeGap_openEdge_mem_connector
    {x y : RlcConnectorVertex 1}
    (hopen : rlc_activeGapDoubleFailureConfig s(x, y) = true) :
    s((x : Site 2), (y : Site 2)) ∈
      rlc_connectorEdges rlc_traceSplitCounterexampleRight
        rlc_traceSplitCounterexampleLeft := by
  have hsupport : s((x : Site 2), (y : Site 2)) ∈
      ({s((![1, -1] : Site 2), ![1, 0]),
        s((![0, 0] : Site 2), ![1, 0]),
        s((![-1, 0] : Site 2), ![0, 0])} :
        Finset (Sym2 (Site 2))) := by
    simpa [rlc_activeGapDoubleFailureConfig, Sym2.map_mk] using hopen
  have heq := rlc_axisGapEdges_eq_connectorEdges_of_origin_mem
    rlc_windingSideCounterexampleGap
    rlc_scaleOne_origin_mem_gapRegionSet
  rw [← heq]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hsupport
  rcases hsupport with hA | hB | hC
  · rw [hA]
    exact rlc_activeGap_sourceA_mem
  · rw [hB]
    exact rlc_activeGap_sourceB_mem
  · rw [hC]
    exact rlc_activeGap_sourceC_mem



theorem rlc_activeDoubleFailure_twoChannel_openSub_le_connector :
    FK.openSub
        (rlc_connectorTwoChannelGraph rlc_traceSplitCounterexampleRight
          rlc_traceSplitCounterexampleLeft)
        rlc_activeGapDoubleFailureConfig ≤
      FK.openSub
        (rlc_connectorFiniteGraph rlc_traceSplitCounterexampleRight
          rlc_traceSplitCounterexampleLeft)
        rlc_activeGapDoubleFailureConfig := by
  intro x y hxy
  rw [FK.openSub_adj] at hxy ⊢
  obtain ⟨⟨hchannel, _hnotTrace⟩, hopen⟩ := hxy
  refine ⟨⟨?_, rlc_activeGap_openEdge_mem_connector hopen⟩, hopen⟩
  exact hchannel.elim (fun hcentral => hcentral.1)
    (fun hreflected => hreflected.1)



theorem rlc_activeDoubleFailure_twoChannel_source_failure :
    rlc_activeGapDoubleFailureConfig ∉
      rlc_finiteTwoChannelConnectorEvent
        rlc_traceSplitCounterexampleRight
        rlc_traceSplitCounterexampleLeft := by
  rintro ⟨x, y, hx, hy, hxy⟩
  exact rlc_activeFullConnector_doubleFailure.1
    ⟨x, y, hx, hy, hxy.mono
      rlc_activeDoubleFailure_twoChannel_openSub_le_connector⟩



theorem rlc_activeDoubleFailure_twoChannel_PIMS_success :
    rlc_connectorCentralFacePIMSConfig
        rlc_traceSplitCounterexampleRight
        rlc_traceSplitCounterexampleLeft
        rlc_activeGapDoubleFailureConfig ∈
      rlc_finiteTwoChannelConnectorEvent
        rlc_traceSplitCounterexampleRight
        rlc_traceSplitCounterexampleLeft :=
  rlc_centralFacePIMS_twoChannel_success_of_closure
    rlc_traceSplitCounterexampleRight
    rlc_traceSplitCounterexampleLeft
    rlc_activeGapDoubleFailureConfig
    rlc_activeDoubleFailure_centralFaceClosurePIMS_success



theorem rlc_activeDoubleFailure_twoChannel_repaired :
    rlc_activeGapDoubleFailureConfig ∉
        rlc_finiteTwoChannelConnectorEvent
          rlc_traceSplitCounterexampleRight
          rlc_traceSplitCounterexampleLeft ∧
      rlc_connectorCentralFacePIMSConfig
          rlc_traceSplitCounterexampleRight
          rlc_traceSplitCounterexampleLeft
          rlc_activeGapDoubleFailureConfig ∈
        rlc_finiteTwoChannelConnectorEvent
          rlc_traceSplitCounterexampleRight
          rlc_traceSplitCounterexampleLeft :=
  ⟨rlc_activeDoubleFailure_twoChannel_source_failure,
    rlc_activeDoubleFailure_twoChannel_PIMS_success⟩



theorem rlc_activeDoubleFailure_twoChannel_singletonMass_le_mergedSuccess :
    rlc_twoChannelForcedDualEventMass
        rlc_traceSplitCounterexampleRight
        rlc_traceSplitCounterexampleLeft (1 / 2) 1
        {rlc_activeGapDoubleFailureConfig} ≤
      FK.bcEventMass
        (rlc_connectorTwoChannelGraph rlc_traceSplitCounterexampleRight
          rlc_traceSplitCounterexampleLeft)
        (rlc_connectorMergedWiring rlc_traceSplitCounterexampleRight
          rlc_traceSplitCounterexampleLeft)
        (1 / 2) 1
        (rlc_finiteTwoChannelConnectorEvent
          rlc_traceSplitCounterexampleRight
          rlc_traceSplitCounterexampleLeft) :=
  rlc_twoChannelForcedDualSingletonMass_le_merged_of_mem
    rlc_traceSplitCounterexampleRight
    rlc_traceSplitCounterexampleLeft
    rlc_activeGapDoubleFailureConfig
    (rlc_connectorCentralFacePIMSConfig
      rlc_traceSplitCounterexampleRight
      rlc_traceSplitCounterexampleLeft
      rlc_activeGapDoubleFailureConfig)
    rlc_activeDoubleFailure_twoChannel_PIMS_success

end

end StatMech.Universality
