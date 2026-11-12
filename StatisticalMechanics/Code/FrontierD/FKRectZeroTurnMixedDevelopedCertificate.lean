/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectZeroTurnDevelopedIncidence











namespace StatMech.FrontierD

noncomputable section



def FKRectZeroTurnOriginalDualSameSideUnique
    (R : FKRectTorus) (omega : R.Configuration) : Prop :=
  ∀ C D : FKRectZeroTurnCutRemainderComponent R omega,
    ∀ X : FKRectRawWiredDualHorizontalCrossingComponent R omega,
      ¬ FKRectZeroTurnUsesPrimalTouchedCrossings R omega C →
      ¬ FKRectZeroTurnUsesPrimalTouchedCrossings R omega D →
      X ∈ fkRectZeroTurnDualTouchedCrossings R omega C →
      X ∈ fkRectZeroTurnDualTouchedCrossings R omega D →
      fkRectZeroTurnRemainderSide R omega C =
        fkRectZeroTurnRemainderSide R omega D → C = D



noncomputable def
    FKRectZeroTurnMixedTouchedCertificate.ofDevelopedIncidence
    (R : FKRectTorus) (omega : R.Configuration)
    (hincidence : FKRectZeroTurnPrimalDevelopedExtremeIncidence R omega)
    (hdual : FKRectZeroTurnOriginalDualSameSideUnique R omega) :
    FKRectZeroTurnMixedTouchedCertificate R omega where
  nonempty := fkRectZeroTurnMixedTouchedCrossings_nonempty R omega
  sameSide_unique := by
    intro C D X hXC hXD hside
    cases X with
    | inl X =>
        have hC :=
          (mem_fkRectZeroTurnMixedTouchedCrossings_inl_iff
            R omega C X).1 hXC
        have hD :=
          (mem_fkRectZeroTurnMixedTouchedCrossings_inl_iff
            R omega D X).1 hXD
        exact fkRectZeroTurnRemainder_eq_of_shared_primalTouchedCrossing
          R omega hincidence C D X hC.2 hD.2 hside
    | inr X =>
        have hC :=
          (mem_fkRectZeroTurnMixedTouchedCrossings_inr_iff
            R omega C X).1 hXC
        have hD :=
          (mem_fkRectZeroTurnMixedTouchedCrossings_inr_iff
            R omega D X).1 hXD
        exact hdual C D X hC.1 hD.1 hC.2 hD.2 hside



noncomputable def
    FKRectZeroTurnMixedTouchedCertificate.ofDisconnectedIncidence
    (R : FKRectTorus) (omega : R.Configuration)
    (hdisconnected :
      FKRectZeroTurnPrimalDevelopedExtremeDisconnectedIncidence R omega)
    (hdual : FKRectZeroTurnOriginalDualSameSideUnique R omega) :
    FKRectZeroTurnMixedTouchedCertificate R omega :=
  FKRectZeroTurnMixedTouchedCertificate.ofDevelopedIncidence R omega
    (fkRectZeroTurnPrimalDevelopedExtremeIncidence_of_disconnected
      R omega hdisconnected)
    hdual


theorem
    fkRectZeroTurnCutRemainderCount_le_two_mul_rawPrimal_add_two_of_disconnectedIncidence
    (R : FKRectTorus) (omega : R.Configuration)
    (hdisconnected :
      FKRectZeroTurnPrimalDevelopedExtremeDisconnectedIncidence R omega)
    (hdual : FKRectZeroTurnOriginalDualSameSideUnique R omega) :
    fkRectZeroTurnCutRemainderCount R omega ≤
      2 * fkRectRawHorizontalCrossingClusterCount R
          (fkRectForceCutClosed R omega) + 2 :=
  fkRectZeroTurnCutRemainderCount_le_two_mul_rawPrimal_add_two_of_touched
    R omega
      (FKRectZeroTurnMixedTouchedCertificate.ofDisconnectedIncidence
        R omega hdisconnected hdual)



noncomputable def
    fkRectZeroTurnMixedTouchedCertificate_of_geometricResidues
    (R : FKRectTorus)
    (hdisconnected : ∀ omega : R.Configuration,
      FKRectZeroTurnPrimalDevelopedExtremeDisconnectedIncidence R omega)
    (hdual : ∀ omega : R.Configuration,
      FKRectZeroTurnOriginalDualSameSideUnique R omega) :
    ∀ omega : R.Configuration,
      FKRectZeroTurnMixedTouchedCertificate R omega :=
  fun omega =>
    FKRectZeroTurnMixedTouchedCertificate.ofDisconnectedIncidence
      R omega (hdisconnected omega) (hdual omega)

end

end StatMech.FrontierD
