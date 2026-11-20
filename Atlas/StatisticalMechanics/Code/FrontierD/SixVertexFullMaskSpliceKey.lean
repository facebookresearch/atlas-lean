/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexLoopFullMaskFineRelation
import Code.FrontierD.SixVertexSpliceKeyLayerSwap









namespace StatMech.FrontierD

noncomputable section


noncomputable def sixVertexFullUnitMaskSplice
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (mask : SixVertexArrows T)
    (hmask : SixVertexFullDisagreementMask
      (source false).arrows (source true).arrows mask) :
    FKColoredStrandSplice source := by
  let target := sixVertexFullDisagreementColoredTarget source mask hmask
  have hcount : fkColoredTrueStrandSlotCount source =
      fkColoredTrueStrandSlotCount target := by
    exact (congrArg Prod.snd
      (sixVertexFullDisagreementColoredTarget_bigrade
        source mask hmask)).symm
  exact FKColoredStrandSplice.ofColorEquiv source target
    (fkColoredStrandSlotEquivOfTrueCount source target hcount)
    (fkColoredStrandSlotEquivOfTrueCount_color source target hcount)

@[simp] theorem sixVertexFullUnitMaskSplice_target
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (mask : SixVertexArrows T)
    (hmask : SixVertexFullDisagreementMask
      (source false).arrows (source true).arrows mask) :
    (sixVertexFullUnitMaskSplice source mask hmask).target =
      sixVertexFullDisagreementColoredTarget source mask hmask := by
  unfold sixVertexFullUnitMaskSplice
  apply FKColoredStrandSplice.ofColorEquiv_target

theorem sixVertexFullUnitMaskSplice_preservesTotalC
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (mask : SixVertexArrows T)
    (hmask : SixVertexFullDisagreementMask
      (source false).arrows (source true).arrows mask) :
    (sixVertexFullUnitMaskSplice source mask hmask).PreservesTotalC := by
  let splice := sixVertexFullUnitMaskSplice source mask hmask
  unfold FKColoredStrandSplice.PreservesTotalC
  rw [← splice.target_totalC_eq_slotPairEqualCount,
    ← fkColoredLoopPairingPairTotalC_eq_slotPairEqualCount,
    sixVertexFullUnitMaskSplice_target]
  exact congrArg Prod.fst
    (sixVertexFullDisagreementColoredTarget_bigrade source mask hmask)

theorem sixVertexFullUnitMaskSplice_seamDelta_false
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (mask : SixVertexArrows T)
    (hmask : SixVertexFullDisagreementMask
      (source false).arrows (source true).arrows mask)
    (htransfer : sixVertexTorusMaskSeamTransfer mask
      (source false).arrows (source true).arrows = 1) :
    (sixVertexFullUnitMaskSplice source mask hmask).seamDelta false = 1 := by
  let splice := sixVertexFullUnitMaskSplice source mask hmask
  have hsplice := splice.target_upCount false
  rw [sixVertexFullUnitMaskSplice_target,
    sixVertexFullDisagreementColoredTarget_arrows] at hsplice
  simp only [Bool.false_eq_true, if_false] at hsplice
  have hswitch := intCast_upCount_switchFirst_eq_add_seamTransfer
    mask (source false).arrows (source true).arrows
  rw [htransfer] at hswitch
  rw [hswitch] at hsplice
  change splice.seamDelta false = 1
  omega

theorem sixVertexFullUnitMaskSplice_seamDelta_true
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (mask : SixVertexArrows T)
    (hmask : SixVertexFullDisagreementMask
      (source false).arrows (source true).arrows mask)
    (htransfer : sixVertexTorusMaskSeamTransfer mask
      (source false).arrows (source true).arrows = 1) :
    (sixVertexFullUnitMaskSplice source mask hmask).seamDelta true = -1 := by
  let splice := sixVertexFullUnitMaskSplice source mask hmask
  have hsplice := splice.target_upCount true
  rw [sixVertexFullUnitMaskSplice_target,
    sixVertexFullDisagreementColoredTarget_arrows] at hsplice
  simp only [if_true] at hsplice
  have hswitch := intCast_upCount_switchSecond_eq_sub_seamTransfer
    mask (source false).arrows (source true).arrows
  rw [htransfer] at hswitch
  rw [hswitch] at hsplice
  change splice.seamDelta true = -1
  omega



noncomputable def sixVertexFullUnitMaskSpliceKey
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (mask : SixVertexArrows T)
    (hmask : SixVertexFullDisagreementMask
      (source false).arrows (source true).arrows mask)
    (htransfer : sixVertexTorusMaskSeamTransfer mask
      (source false).arrows (source true).arrows = 1) :
    FKColoredFineTwoCycleUnitTransferSpliceKey source where
  splice := sixVertexFullUnitMaskSplice source mask hmask
  preservesTotalC := sixVertexFullUnitMaskSplice_preservesTotalC
    source mask hmask
  seamDelta_false := sixVertexFullUnitMaskSplice_seamDelta_false
    source mask hmask htransfer
  seamDelta_true := sixVertexFullUnitMaskSplice_seamDelta_true
    source mask hmask htransfer
  fine := by
    rw [sixVertexFullUnitMaskSplice_target]
    exact sixVertexFullDisagreementColoredTarget_boundedFineRowProfile
      source mask hmask
  twoCycle := by
    rw [sixVertexFullUnitMaskSplice_target,
      sixVertexFullDisagreementColoredTarget_arrows,
      sixVertexFullDisagreementColoredTarget_arrows]
    exact hmask.pairAtMostTwoCycleFineRelated.1

@[simp] theorem sixVertexFullUnitMaskSpliceKey_target
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (mask : SixVertexArrows T)
    (hmask : SixVertexFullDisagreementMask
      (source false).arrows (source true).arrows mask)
    (htransfer : sixVertexTorusMaskSeamTransfer mask
      (source false).arrows (source true).arrows = 1) :
    (sixVertexFullUnitMaskSpliceKey source mask hmask htransfer).splice.target =
      sixVertexFullDisagreementColoredTarget source mask hmask :=
  sixVertexFullUnitMaskSplice_target source mask hmask

end

end StatMech.FrontierD
