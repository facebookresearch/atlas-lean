/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexPositiveUnitComponentResidualRouting
import Code.FrontierD.SixVertexFourByTwoActiveKeyRepair









namespace StatMech.FrontierD

noncomputable section



noncomputable def sixVertexFourByTwoActiveCycleRepairLoopTarget :
    SixVertexHorizontalDegreeTwoLoopHallTarget sixVertexFourByTwoTorus
      sixVertexFourByTwoSectorOne
      sixVertexFourByTwoActiveObstructionGrade := by
  let physical := sixVertexFourByTwoActiveCycleRepairPhysicalTarget
  let firstPairing : SixVertexCompatibleLoopPairing physical.1.1.1 :=
    ⟨fun vertex => sixVertexPreferredCompatiblePairing
        physical.1.1.1 vertex,
      sixVertexPreferredCompatiblePairing_compatible
        physical.1.1.1 physical.1.1.2.1⟩
  let secondPairing : SixVertexCompatibleLoopPairing physical.1.2.1 :=
    ⟨fun vertex => sixVertexPreferredCompatiblePairing
        physical.1.2.1 vertex,
      sixVertexPreferredCompatiblePairing_compatible
        physical.1.2.1 physical.1.2.2.1⟩
  refine ⟨⟨physical.1, firstPairing, secondPairing⟩, ?_⟩
  rw [sixVertexLoopDecoratedPairBigrade_eq_configurationPair]
  exact physical.2



noncomputable def
    sixVertexFourByTwoActiveObstructionResidualGeometricCertificate :
    SixVertexHorizontalResidualGeometricCertificate
      (hmiddle_pos := sixVertexFourByTwoActiveObstructionMiddle_pos)
      (hmiddle_lt := sixVertexFourByTwoActiveObstructionMiddle_lt)
      (sixVertexHorizontalHallSourceCanonicalLoop
        (hmiddle_pos := sixVertexFourByTwoActiveObstructionMiddle_pos)
        (hmiddle_lt := sixVertexFourByTwoActiveObstructionMiddle_lt)
        sixVertexFourByTwoActiveObstructionToken) :=
  .fineRelated sixVertexFourByTwoActiveCycleRepairLoopTarget (by
    change sixVertexPairAtMostTwoCycleFineRelated
      ((sixVertexHorizontalActualDeficitConfigurationPair
          sixVertexFourByTwoActiveObstructionToken).1.1.1,
        (sixVertexHorizontalActualDeficitConfigurationPair
          sixVertexFourByTwoActiveObstructionToken).1.2.1)
      (sixVertexFourByTwoCycleMiddleFirst,
        sixVertexFourByTwoCycleMiddleSecond)
    rw [sixVertexFourByTwoActiveObstructionConfigurationPair_eq]
    exact sixVertexFourByTwo_cycleMiddle_fineRelated)



noncomputable def sixVertexFourByTwoActiveObstructionResidualGeometricRepair :
    SixVertexHorizontalResidualGeometricSurplusRepair
      (hmiddle_pos := sixVertexFourByTwoActiveObstructionMiddle_pos)
      (hmiddle_lt := sixVertexFourByTwoActiveObstructionMiddle_lt)
      sixVertexFourByTwoActiveObstructionToken :=
  SixVertexHorizontalResidualGeometricSurplusRepair.ofCertificateSourceWeightZero
    sixVertexFourByTwoActiveObstructionToken
    sixVertexFourByTwoActiveObstructionResidualGeometricCertificate
    sixVertexFourByTwoActiveCycleRepairProfile_sourceWeight_eq_zero


theorem sixVertexFourByTwoActiveObstructionResidualGeometricRepair_supported :
    sixVertexHorizontalOffDiagonalTwoCycleSupport
      sixVertexFourByTwoTorus sixVertexFourByTwoSectorOne
      sixVertexFourByTwoActiveObstructionMiddle_pos
      sixVertexFourByTwoActiveObstructionMiddle_lt
      sixVertexFourByTwoActiveObstructionGrade
      sixVertexFourByTwoActiveObstructionToken
      sixVertexFourByTwoActiveObstructionResidualGeometricRepair.target :=
  sixVertexFourByTwoActiveObstructionResidualGeometricRepair.supported

end

end StatMech.FrontierD
