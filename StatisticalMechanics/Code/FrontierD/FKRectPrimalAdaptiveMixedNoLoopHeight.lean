/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectPrimalAdaptiveMixedNoLoop
import Code.FrontierD.FKRectZeroTurnMixedDevelopedCertificate









namespace StatMech.FrontierD

noncomputable section



theorem fkRectCritical_zeroTurnAbove_le_half_of_mixedAnnulusCharge_height
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q)
    (charge : ∀ omega : R.Configuration,
      FKRectZeroTurnMixedAnnulusCharge R omega) :
    fkRectCriticalZeroTurnAboveMass R q
        (2 * R.width + 2 * R.height + 2) ≤ (1 : Real) / 2 := by
  apply fkRectCritical_zeroTurnAbove_le_half_of_mixedAnnulusCharge
    R hq charge R.height
  simp only [Nat.choose_succ_self, Nat.cast_zero, zero_mul]
  have hc : 0 < FK.cFE (fkRectCriticalP q) q :=
    FK.cFE_pos
      (fkRectCriticalP_pos (lt_of_lt_of_le zero_lt_one hq))
      (fkRectCriticalP_lt_one (lt_of_lt_of_le zero_lt_one hq)) hq
  positivity



theorem zeroTurnCost_div_two_q_le_allSectorNormalization_of_mixedAnnulusCharge_height
    (R : FKRectTorus) {q : Real} (hq : 4 < q)
    (charge : ∀ omega : R.Configuration,
      FKRectZeroTurnMixedAnnulusCharge R omega) :
    (2 / Real.sqrt q) ^ (2 * R.width + 2 * R.height + 2) / (2 * q) ≤
      fkRectAllSectorNormalization R q := by
  apply zeroTurnCost_div_two_q_le_allSectorNormalization_of_mixedAnnulusCharge
    R hq charge R.height
  simp only [Nat.choose_succ_self, Nat.cast_zero, zero_mul]
  have hq1 : 1 ≤ q := by linarith
  have hc : 0 < FK.cFE (fkRectCriticalP q) q :=
    FK.cFE_pos
      (fkRectCriticalP_pos (lt_of_lt_of_le zero_lt_one hq1))
      (fkRectCriticalP_lt_one (lt_of_lt_of_le zero_lt_one hq1)) hq1
  positivity



theorem zeroTurnCost_div_two_q_le_allSectorNormalization_of_mixedTouchedCrossings_height
    (R : FKRectTorus) {q : Real} (hq : 4 < q)
    (certificate : ∀ omega : R.Configuration,
      FKRectZeroTurnMixedTouchedCertificate R omega) :
    (2 / Real.sqrt q) ^ (2 * R.width + 2 * R.height + 2) / (2 * q) ≤
      fkRectAllSectorNormalization R q := by
  apply zeroTurnCost_div_two_q_le_allSectorNormalization_of_mixedTouchedCrossings
    R hq certificate R.height
  simp only [Nat.choose_succ_self, Nat.cast_zero, zero_mul]
  have hq1 : 1 ≤ q := by linarith
  have hc : 0 < FK.cFE (fkRectCriticalP q) q :=
    FK.cFE_pos
      (fkRectCriticalP_pos (lt_of_lt_of_le zero_lt_one hq1))
      (fkRectCriticalP_lt_one (lt_of_lt_of_le zero_lt_one hq1)) hq1
  positivity



theorem zeroTurnCost_div_two_q_le_allSectorNormalization_of_geometricResidues_height
    (R : FKRectTorus) {q : Real} (hq : 4 < q)
    (hdisconnected : ∀ omega : R.Configuration,
      FKRectZeroTurnPrimalDevelopedExtremeDisconnectedIncidence R omega)
    (hdual : ∀ omega : R.Configuration,
      FKRectZeroTurnOriginalDualSameSideUnique R omega) :
    (2 / Real.sqrt q) ^ (2 * R.width + 2 * R.height + 2) / (2 * q) ≤
      fkRectAllSectorNormalization R q := by
  apply
    zeroTurnCost_div_two_q_le_allSectorNormalization_of_mixedTouchedCrossings_height
      R hq
  exact fkRectZeroTurnMixedTouchedCertificate_of_geometricResidues
    R hdisconnected hdual




theorem zeroTurnCost_div_two_q_le_allSectorNormalization_of_regularNeighborhood_height
    (R : FKRectTorus) {q : Real} (hq : 4 < q)
    (hregular : ∀ omega : R.Configuration,
      FKRectPrimalRankOneRegularNeighborhood R omega)
    (hdual : ∀ omega : R.Configuration,
      FKRectZeroTurnOriginalDualSameSideUnique R omega) :
    (2 / Real.sqrt q) ^ (2 * R.width + 2 * R.height + 2) / (2 * q) ≤
      fkRectAllSectorNormalization R q := by
  apply
    zeroTurnCost_div_two_q_le_allSectorNormalization_of_geometricResidues_height
      R hq
  · intro omega
    exact
      fkRectZeroTurnPrimalDevelopedExtremeDisconnectedIncidence_of_regularNeighborhood
        R omega (hregular omega)
  · exact hdual

end

end StatMech.FrontierD
