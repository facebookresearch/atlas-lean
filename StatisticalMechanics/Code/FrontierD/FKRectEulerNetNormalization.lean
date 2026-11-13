/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.FKRectEulerNetIdentification
import Code.FrontierD.FKRectBalancedSectorNormalization

open Finset

namespace StatMech.FrontierD

noncomputable section



theorem fkRectRandomClusterWeight_critical_eq_loop_netIndicator
    (R : FKRectTorus) {q : Real} (hq : 0 < q)
    (omega : R.Configuration) :
    fkRectRandomClusterWeight R (fkRectCriticalP q) q omega =
      fkRectCriticalLoopNormalization R q *
        Real.sqrt q ^ fkRectMedialLoopCount R omega *
          q ^ fkRectNetIndicator R omega := by
  exact fkRectRandomClusterWeight_critical_eq_loop_net R hq omega
    (fkRectNetIndicator R omega)
    (fkRectEulerHomologyDefect_eq_two_mul_netIndicator_configuration R omega)



theorem fkRectZeroTurnEulerResidual_eq_netIndicator
    (R : FKRectTorus) {q : Real} (hq : 4 < q)
    (omega : R.Configuration) :
    fkRectZeroTurnEulerResidual R q omega =
      (2 / Real.sqrt q) ^ fkRectZeroTurnLoopCount R omega /
        q ^ fkRectNetIndicator R omega := by
  unfold fkRectZeroTurnEulerResidual
  rw [fkRectEulerHomologyDefect_eq_two_mul_netIndicator_configuration]
  have hq0 : 0 ≤ q := by linarith
  let s := fkRectNetIndicator R omega
  change (2 / Real.sqrt q) ^ fkRectZeroTurnLoopCount R omega /
      Real.sqrt q ^ (2 * (s : Int)) =
    (2 / Real.sqrt q) ^ fkRectZeroTurnLoopCount R omega / q ^ s
  have hs : Real.sqrt q ≠ 0 := (Real.sqrt_pos.2 (by linarith)).ne'
  rw [show 2 * (s : Int) = (2 * s : Nat) by omega, zpow_natCast,
    pow_mul, Real.sq_sqrt hq0]



theorem fkRectAllOrientedLoopTilt_eq_zeroTurn_netIndicator_fkQgt4
    (R : FKRectTorus) {q : Real} (hq : 4 < q)
    (omega : R.Configuration) :
    let lam := sixVertexAntiferroelectricLambda (fkQgt4SixVertexWeight q)
    fkRectAllOrientedLoopTilt R q lam omega =
      ((2 / Real.sqrt q) ^ fkRectZeroTurnLoopCount R omega /
          q ^ fkRectNetIndicator R omega) /
        Real.sqrt q ^ (R.width * R.height : Nat) := by
  dsimp only
  rw [fkRectAllOrientedLoopTilt_eq_residual_div_area_fkQgt4 R hq,
    fkRectZeroTurnEulerResidual_eq_netIndicator R hq]



def fkRectAllSectorNormalization (R : FKRectTorus) (q : Real) : Real :=
  Real.sqrt q ^ (R.width * R.height : Nat) *
    (sixVertexTorusArrowPartitionSum R.medialTorus
        (fkQgt4SixVertexWeight q) / fkRectCriticalReducedZ R q)



theorem fkRectAllSectorNormalization_eq_residualExpectation
    (R : FKRectTorus) {q : Real} (hq : 4 < q) :
    fkRectAllSectorNormalization R q =
      ∑ omega : R.Configuration,
        fkRectCriticalRandomClusterProb R q omega *
          fkRectZeroTurnEulerResidual R q omega := by
  let lam := sixVertexAntiferroelectricLambda (fkQgt4SixVertexWeight q)
  have hloop : fkRectOrientedLoopPartitionSum R lam =
      sixVertexTorusArrowPartitionSum R.medialTorus
        (fkQgt4SixVertexWeight q) := by
    rw [fkRectOrientedLoopPartitionSum_eq_sixVertex]
    exact congrArg (sixVertexTorusArrowPartitionSum R.medialTorus)
      (exp_half_add_exp_neg_half_sixVertexLambda_fkQgt4 hq)
  have hexpect := sum_rcProb_mul_windingRestrictedAllOrientedLoopTilt
    R (by linarith : 0 < q) lam 0
  simp only [Nat.zero_le, if_true] at hexpect
  have hraw :
      (∑ omega : R.Configuration,
        fkRectCriticalRandomClusterProb R q omega *
          fkRectAllOrientedLoopTilt R q lam omega) =
        sixVertexTorusArrowPartitionSum R.medialTorus
            (fkQgt4SixVertexWeight q) /
          fkRectCriticalReducedZ R q := by
    rw [hexpect]
    exact congrArg (fun x => x / fkRectCriticalReducedZ R q) hloop
  have hres := sum_rcProb_mul_windingRestrictedAllTilt_eq_residual_div_area
    R hq 0
  simp only [Nat.zero_le, if_true] at hres
  have harea : Real.sqrt q ^ (R.width * R.height : Nat) ≠ 0 := by
    positivity
  unfold fkRectAllSectorNormalization
  rw [← hraw, hres]
  field_simp


theorem fkRectAllSectorNormalization_eq_zeroTurnNetExpectation
    (R : FKRectTorus) {q : Real} (hq : 4 < q) :
    fkRectAllSectorNormalization R q =
      ∑ omega : R.Configuration,
        fkRectCriticalRandomClusterProb R q omega *
          ((2 / Real.sqrt q) ^ fkRectZeroTurnLoopCount R omega /
            q ^ fkRectNetIndicator R omega) := by
  rw [fkRectAllSectorNormalization_eq_residualExpectation R hq]
  apply Finset.sum_congr rfl
  intro omega homega
  rw [fkRectZeroTurnEulerResidual_eq_netIndicator R hq]


theorem sixVertexTorusFixedCharge_zero_eq_balanced
    (T : EvenTorus) (c : Real) :
    sixVertexTorusFixedChargePartitionSum T 0 (Nat.zero_le _) c =
      svTorusBalancedArrowPartitionSum T c := by
  rw [sixVertexTorusFixedChargePartitionSum_eq_sectorTrace,
    svTorusBalancedArrowPartitionSum_eq_sectorTrace]
  simp only [Nat.sub_zero]



theorem sixVertexTorusFixedCharge_zero_le_arrowPartitionSum
    (T : EvenTorus) {c : Real} (hc : 0 ≤ c) :
    sixVertexTorusFixedChargePartitionSum T 0 (Nat.zero_le _) c ≤
      sixVertexTorusArrowPartitionSum T c := by
  rw [sixVertexTorusFixedCharge_zero_eq_balanced]
  rw [← sixVertexRectangleBalancedPartitionSum_eq_torusBalancedArrow]
  exact sixVertexRectangleBalancedPartitionSum_le_torusArrowPartitionSum
    T hc



theorem fkRectBalancedSectorNormalization_le_allSectorNormalization
    (R : FKRectTorus) {q : Real} (hq : 4 < q) :
    fkRectBalancedSectorNormalization R q ≤
      fkRectAllSectorNormalization R q := by
  unfold fkRectBalancedSectorNormalization fkRectAllSectorNormalization
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply div_le_div_of_nonneg_right _
    (fkRectCriticalReducedZ_pos R (by linarith)).le
  exact sixVertexTorusFixedCharge_zero_le_arrowPartitionSum
    R.medialTorus (by
      linarith [two_lt_fkQgt4SixVertexWeight hq])

theorem fkRectAllSectorNormalization_pos
    (R : FKRectTorus) {q : Real} (hq : 4 < q) :
    0 < fkRectAllSectorNormalization R q :=
  (fkRectBalancedSectorNormalization_pos R hq).trans_le
    (fkRectBalancedSectorNormalization_le_allSectorNormalization R hq)

theorem fkRectAllSectorNormalization_le_one
    (R : FKRectTorus) {q : Real} (hq : 4 < q) :
    fkRectAllSectorNormalization R q ≤ 1 := by
  rw [fkRectAllSectorNormalization_eq_residualExpectation R hq]
  calc
    (∑ omega : R.Configuration,
        fkRectCriticalRandomClusterProb R q omega *
          fkRectZeroTurnEulerResidual R q omega) ≤
        ∑ omega : R.Configuration,
          fkRectCriticalRandomClusterProb R q omega := by
      apply Finset.sum_le_sum
      intro omega homega
      exact mul_le_of_le_one_right
        (fkRectCriticalRandomClusterProb_nonneg R (by linarith) omega)
        (fkRectZeroTurnEulerResidual_le_one R hq omega)
    _ = 1 := sum_fkRectCriticalRandomClusterProb R (by linarith)



def fkRectBalancedSectorShare (R : FKRectTorus) (q : Real) : Real :=
  fkRectBalancedSectorNormalization R q /
    fkRectAllSectorNormalization R q

theorem fkRectBalancedSectorShare_mem_Ioc
    (R : FKRectTorus) {q : Real} (hq : 4 < q) :
    fkRectBalancedSectorShare R q ∈ Set.Ioc 0 1 := by
  constructor
  · exact div_pos (fkRectBalancedSectorNormalization_pos R hq)
      (fkRectAllSectorNormalization_pos R hq)
  · exact (div_le_one (fkRectAllSectorNormalization_pos R hq)).2
      (fkRectBalancedSectorNormalization_le_allSectorNormalization R hq)



theorem fkRectBalancedSectorNormalization_eq_share_mul_all
    (R : FKRectTorus) {q : Real} (hq : 4 < q) :
    fkRectBalancedSectorNormalization R q =
      fkRectBalancedSectorShare R q * fkRectAllSectorNormalization R q := by
  unfold fkRectBalancedSectorShare
  rw [div_mul_cancel₀]
  exact (fkRectAllSectorNormalization_pos R hq).ne'



theorem fkRectBalancedSectorShare_eq_sixVertexRatio
    (R : FKRectTorus) {q : Real} (hq : 4 < q) :
    fkRectBalancedSectorShare R q =
      sixVertexTorusFixedChargePartitionSum R.medialTorus 0
          (Nat.zero_le _) (fkQgt4SixVertexWeight q) /
        sixVertexTorusArrowPartitionSum R.medialTorus
          (fkQgt4SixVertexWeight q) := by
  unfold fkRectBalancedSectorShare fkRectBalancedSectorNormalization
    fkRectAllSectorNormalization
  have harea : Real.sqrt q ^ (R.width * R.height : Nat) ≠ 0 := by
    positivity
  have hZ : fkRectCriticalReducedZ R q ≠ 0 :=
    (fkRectCriticalReducedZ_pos R (by linarith)).ne'
  have hfull : sixVertexTorusArrowPartitionSum R.medialTorus
      (fkQgt4SixVertexWeight q) ≠ 0 := by
    intro hzero
    have hall := fkRectAllSectorNormalization_pos R hq
    simp [fkRectAllSectorNormalization, hzero] at hall
  field_simp


theorem balancedNormalization_negLog_eq_all_add_share
    (R : FKRectTorus) {q : Real} (hq : 4 < q) :
    -Real.log (fkRectBalancedSectorNormalization R q) =
      -Real.log (fkRectAllSectorNormalization R q) +
        -Real.log (fkRectBalancedSectorShare R q) := by
  rw [fkRectBalancedSectorNormalization_eq_share_mul_all R hq,
    Real.log_mul
      (fkRectBalancedSectorShare_mem_Ioc R hq).1.ne'
      (fkRectAllSectorNormalization_pos R hq).ne']
  ring

end

end StatMech.FrontierD
