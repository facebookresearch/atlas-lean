/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.RSWConnectorTwoChannelFullPhysicalTerminalResidueCounterexample









namespace StatMech.Universality

noncomputable section




theorem
    rlc_twoChannelPIMSPooledVisibleFibreCapacity_of_retainedAnchor_staticCut
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hinc : RlcBookFaithfulRetainedAnchorIncidence gamma gamma')
    (hstatic : RlcTwoChannelFullPhysicalStaticCutIntersection
      gamma gamma' hinc.1) :
    RlcTwoChannelPIMSPooledVisibleFibreCapacity
      (rlc_twoChannelClosureFailureCertificate_of_centralFace gamma gamma'
        (rlc_centralFaceClosureFailureCertificate_of_retainedAnchorIncidence
          hinc)) := by
  apply rlc_twoChannelPIMSPooledVisibleFibreCapacity_of_fullPhysicalSuccess
    _ hinc.1
  exact rlc_twoChannelFullPhysicalPermutationSuccess_of_staticCutIntersection
    hinc.1 hstatic




theorem
    rlc_finiteTwoChannelConnectorMass_selfDual_ge_of_retainedAnchor_staticCut
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hinc : RlcBookFaithfulRetainedAnchorIncidence gamma gamma')
    (hstatic : RlcTwoChannelFullPhysicalStaticCutIntersection
      gamma gamma' hinc.1)
    {q : Real} (hq : 1 <= q) (N : Nat)
    (hscore : RlcTwoChannelFullPhysicalPermutationScoreDefect
      gamma gamma' N) :
    1 / (1 + (Real.sqrt q) ^ N * q) <=
      FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma')
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteTwoChannelConnectorEvent gamma gamma') := by
  let hclosure :=
    rlc_twoChannelClosureFailureCertificate_of_centralFace gamma gamma'
      (rlc_centralFaceClosureFailureCertificate_of_retainedAnchorIncidence
        hinc)
  apply
    rlc_finiteTwoChannelConnectorMass_selfDual_ge_of_fullPhysicalSuccess_scoreDefect
      hclosure hinc.1
      (rlc_twoChannelFullPhysicalPermutationSuccess_of_staticCutIntersection
        hinc.1 hstatic)
      hq N hscore



theorem
    rlc_finiteTwoChannelConnectorMass_selfDual_ge_half_of_retainedAnchor_staticCut
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hinc : RlcBookFaithfulRetainedAnchorIncidence gamma gamma')
    (hstatic : RlcTwoChannelFullPhysicalStaticCutIntersection
      gamma gamma' hinc.1) :
    (1 / 2 : Real) <=
      FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma')
        (BeffaraDC.selfDualPoint 1) 1
        (rlc_finiteTwoChannelConnectorEvent gamma gamma') := by
  let hclosure :=
    rlc_twoChannelClosureFailureCertificate_of_centralFace gamma gamma'
      (rlc_centralFaceClosureFailureCertificate_of_retainedAnchorIncidence
        hinc)
  exact
    rlc_finiteTwoChannelConnectorMass_selfDual_ge_half_of_fullPhysicalSuccess
      hclosure hinc.1
      (rlc_twoChannelFullPhysicalPermutationSuccess_of_staticCutIntersection
        hinc.1 hstatic)

end

end StatMech.Universality
