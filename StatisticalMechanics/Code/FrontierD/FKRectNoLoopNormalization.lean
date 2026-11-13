/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectEulerNetNormalization
import Code.FrontierD.FKRectRandomClusterFiniteEnergy









open Finset Filter Topology

namespace StatMech.FrontierD

noncomputable section



def fkRectCriticalZeroTurnAtMostMass
    (R : FKRectTorus) (q : Real) (L : Nat) : Real :=
  ∑ omega : R.Configuration,
    if fkRectZeroTurnLoopCount R omega ≤ L then
      fkRectCriticalRandomClusterProb R q omega
    else 0



def fkRectCriticalZeroTurnAboveMass
    (R : FKRectTorus) (q : Real) (L : Nat) : Real :=
  ∑ omega : R.Configuration,
    if L < fkRectZeroTurnLoopCount R omega then
      fkRectCriticalRandomClusterProb R q omega
    else 0



def fkRectCriticalZeroTurnExpectation
    (R : FKRectTorus) (q : Real) : Real :=
  ∑ omega : R.Configuration,
    fkRectCriticalRandomClusterProb R q omega *
      fkRectZeroTurnLoopCount R omega

theorem fkRectCriticalZeroTurnAtMostMass_nonneg
    (R : FKRectTorus) {q : Real} (hq : 0 < q) (L : Nat) :
    0 ≤ fkRectCriticalZeroTurnAtMostMass R q L := by
  unfold fkRectCriticalZeroTurnAtMostMass
  apply Finset.sum_nonneg
  intro omega homega
  split
  · exact fkRectCriticalRandomClusterProb_nonneg R hq omega
  · exact le_rfl

theorem fkRectCriticalZeroTurnAtMostMass_le_one
    (R : FKRectTorus) {q : Real} (hq : 0 < q) (L : Nat) :
    fkRectCriticalZeroTurnAtMostMass R q L ≤ 1 := by
  unfold fkRectCriticalZeroTurnAtMostMass
  calc
    (∑ omega : R.Configuration,
        if fkRectZeroTurnLoopCount R omega ≤ L then
          fkRectCriticalRandomClusterProb R q omega else 0) ≤
        ∑ omega : R.Configuration,
          fkRectCriticalRandomClusterProb R q omega := by
      apply Finset.sum_le_sum
      intro omega homega
      split
      · exact le_rfl
      · exact fkRectCriticalRandomClusterProb_nonneg R hq omega
    _ = 1 := sum_fkRectCriticalRandomClusterProb R hq

theorem fkRectCriticalZeroTurnAboveMass_nonneg
    (R : FKRectTorus) {q : Real} (hq : 0 < q) (L : Nat) :
    0 ≤ fkRectCriticalZeroTurnAboveMass R q L := by
  unfold fkRectCriticalZeroTurnAboveMass
  apply Finset.sum_nonneg
  intro omega homega
  split
  · exact fkRectCriticalRandomClusterProb_nonneg R hq omega
  · exact le_rfl

theorem fkRectCriticalZeroTurnExpectation_nonneg
    (R : FKRectTorus) {q : Real} (hq : 0 < q) :
    0 ≤ fkRectCriticalZeroTurnExpectation R q := by
  unfold fkRectCriticalZeroTurnExpectation
  apply Finset.sum_nonneg
  intro omega homega
  exact mul_nonneg (fkRectCriticalRandomClusterProb_nonneg R hq omega)
    (Nat.cast_nonneg _)


theorem zeroTurnAboveMass_mul_succ_le_expectation
    (R : FKRectTorus) {q : Real} (hq : 0 < q) (L : Nat) :
    ((L + 1 : Nat) : Real) *
        fkRectCriticalZeroTurnAboveMass R q L ≤
      fkRectCriticalZeroTurnExpectation R q := by
  unfold fkRectCriticalZeroTurnAboveMass
    fkRectCriticalZeroTurnExpectation
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro omega homega
  by_cases habove : L < fkRectZeroTurnLoopCount R omega
  · rw [if_pos habove]
    have hcast : ((L + 1 : Nat) : Real) ≤
        (fkRectZeroTurnLoopCount R omega : Real) := by
      exact_mod_cast Nat.succ_le_of_lt habove
    have hprob := fkRectCriticalRandomClusterProb_nonneg R hq omega
    nlinarith
  · rw [if_neg habove, mul_zero]
    exact mul_nonneg (fkRectCriticalRandomClusterProb_nonneg R hq omega)
      (Nat.cast_nonneg _)



theorem aboveMass_le_half_of_expectation_le_half_succ
    (R : FKRectTorus) {q : Real} (hq : 0 < q) (L : Nat)
    (hmoment : fkRectCriticalZeroTurnExpectation R q ≤
      ((L + 1 : Nat) : Real) / 2) :
    fkRectCriticalZeroTurnAboveMass R q L ≤ (1 : Real) / 2 := by
  have hmarkov := zeroTurnAboveMass_mul_succ_le_expectation R hq L
  have hL : (0 : Real) < ((L + 1 : Nat) : Real) := by positivity
  nlinarith



theorem fkRectCriticalZeroTurnAtMostMass_add_aboveMass
    (R : FKRectTorus) {q : Real} (hq : 0 < q) (L : Nat) :
    fkRectCriticalZeroTurnAtMostMass R q L +
        fkRectCriticalZeroTurnAboveMass R q L = 1 := by
  unfold fkRectCriticalZeroTurnAtMostMass
    fkRectCriticalZeroTurnAboveMass
  rw [← Finset.sum_add_distrib]
  calc
    (∑ omega : R.Configuration,
        ((if fkRectZeroTurnLoopCount R omega ≤ L then
            fkRectCriticalRandomClusterProb R q omega else 0) +
          if L < fkRectZeroTurnLoopCount R omega then
            fkRectCriticalRandomClusterProb R q omega else 0)) =
        ∑ omega : R.Configuration,
          fkRectCriticalRandomClusterProb R q omega := by
      apply Finset.sum_congr rfl
      intro omega homega
      by_cases hcount : fkRectZeroTurnLoopCount R omega ≤ L
      · have hnot : ¬ L < fkRectZeroTurnLoopCount R omega :=
          Nat.not_lt.mpr hcount
        simp [hcount, hnot]
      · have habove : L < fkRectZeroTurnLoopCount R omega :=
          Nat.lt_of_not_ge hcount
        simp [hcount, habove]
    _ = 1 := sum_fkRectCriticalRandomClusterProb R hq

theorem half_le_fkRectCriticalZeroTurnAtMostMass_of_aboveMass_le_half
    (R : FKRectTorus) {q : Real} (hq : 0 < q) (L : Nat)
    (htail : fkRectCriticalZeroTurnAboveMass R q L ≤ (1 : Real) / 2) :
    (1 : Real) / 2 ≤ fkRectCriticalZeroTurnAtMostMass R q L := by
  have hpartition :=
    fkRectCriticalZeroTurnAtMostMass_add_aboveMass R hq L
  linarith



theorem zeroTurnResidual_lower_of_count_le
    (R : FKRectTorus) {q : Real} (hq : 4 < q)
    (omega : R.Configuration) {L : Nat}
    (hcount : fkRectZeroTurnLoopCount R omega ≤ L) :
    (2 / Real.sqrt q) ^ L / q ≤
      fkRectZeroTurnEulerResidual R q omega := by
  let a : Real := 2 / Real.sqrt q
  have hq0 : 0 < q := by linarith
  have ha0 : 0 ≤ a := by dsimp [a]; positivity
  have hsqrt : 2 < Real.sqrt q := by
    have hs := Real.sq_sqrt (show 0 ≤ q by linarith)
    have hs0 := Real.sqrt_nonneg q
    nlinarith
  have ha1 : a ≤ 1 := by
    dsimp [a]
    exact (div_le_one (Real.sqrt_pos.2 hq0)).2 hsqrt.le
  have hpow : a ^ L ≤ a ^ fkRectZeroTurnLoopCount R omega :=
    pow_le_pow_of_le_one ha0 ha1 hcount
  have hs := fkRectNetIndicator_le_one R omega
  rcases (Nat.le_one_iff_eq_zero_or_eq_one.mp hs) with hs0 | hs1
  · rw [fkRectZeroTurnEulerResidual_eq_netIndicator R hq, hs0]
    simp only [pow_zero, div_one]
    calc
      a ^ L / q ≤ a ^ L := by
        rw [div_le_iff₀ hq0]
        nlinarith [pow_nonneg ha0 L]
      _ ≤ a ^ fkRectZeroTurnLoopCount R omega := hpow
  · rw [fkRectZeroTurnEulerResidual_eq_netIndicator R hq, hs1, pow_one]
    exact div_le_div_of_nonneg_right hpow hq0.le




theorem zeroTurnCost_mul_atMostMass_le_allSectorNormalization
    (R : FKRectTorus) {q : Real} (hq : 4 < q) (L : Nat) :
    ((2 / Real.sqrt q) ^ L / q) *
        fkRectCriticalZeroTurnAtMostMass R q L ≤
      fkRectAllSectorNormalization R q := by
  rw [fkRectAllSectorNormalization_eq_residualExpectation R hq]
  unfold fkRectCriticalZeroTurnAtMostMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro omega homega
  by_cases hcount : fkRectZeroTurnLoopCount R omega ≤ L
  · rw [if_pos hcount]
    simpa [mul_comm] using mul_le_mul_of_nonneg_left
      (zeroTurnResidual_lower_of_count_le R hq omega hcount)
      (fkRectCriticalRandomClusterProb_nonneg R (by linarith) omega)
  · rw [if_neg hcount, mul_zero]
    exact mul_nonneg
      (fkRectCriticalRandomClusterProb_nonneg R (by linarith) omega)
      (fkRectZeroTurnEulerResidual_nonneg R hq omega)



theorem zeroTurnCost_div_two_q_le_allSectorNormalization
    (R : FKRectTorus) {q : Real} (hq : 4 < q) (L : Nat)
    (hmass : (1 : Real) / 2 ≤
      fkRectCriticalZeroTurnAtMostMass R q L) :
    (2 / Real.sqrt q) ^ L / (2 * q) ≤
      fkRectAllSectorNormalization R q := by
  have hcost : 0 ≤ (2 / Real.sqrt q) ^ L / q := by positivity
  calc
    (2 / Real.sqrt q) ^ L / (2 * q) =
        ((2 / Real.sqrt q) ^ L / q) * ((1 : Real) / 2) := by
      field_simp
    _ ≤ ((2 / Real.sqrt q) ^ L / q) *
        fkRectCriticalZeroTurnAtMostMass R q L :=
      mul_le_mul_of_nonneg_left hmass hcost
    _ ≤ fkRectAllSectorNormalization R q :=
      zeroTurnCost_mul_atMostMass_le_allSectorNormalization R hq L


theorem zeroTurnCost_div_two_q_le_allSectorNormalization_of_aboveMass_le_half
    (R : FKRectTorus) {q : Real} (hq : 4 < q) (L : Nat)
    (htail : fkRectCriticalZeroTurnAboveMass R q L ≤ (1 : Real) / 2) :
    (2 / Real.sqrt q) ^ L / (2 * q) ≤
      fkRectAllSectorNormalization R q :=
  zeroTurnCost_div_two_q_le_allSectorNormalization R hq L
    (half_le_fkRectCriticalZeroTurnAtMostMass_of_aboveMass_le_half R
      (by linarith) L htail)


theorem zeroTurnCost_div_two_q_le_allSectorNormalization_of_expectation
    (R : FKRectTorus) {q : Real} (hq : 4 < q) (L : Nat)
    (hmoment : fkRectCriticalZeroTurnExpectation R q ≤
      ((L + 1 : Nat) : Real) / 2) :
    (2 / Real.sqrt q) ^ L / (2 * q) ≤
      fkRectAllSectorNormalization R q :=
  zeroTurnCost_div_two_q_le_allSectorNormalization_of_aboveMass_le_half
    R hq L
      (aboveMass_le_half_of_expectation_le_half_succ R (by linarith) L hmoment)



theorem tendsto_allSectorNormalization_negLog_div_height_zero_of_lower
    (R : Nat → FKRectTorus) {q : Real} (hq : 4 < q)
    (lower : Nat → Real)
    (hlowerPos : ∀ n, 0 < lower n)
    (hlower : ∀ n, lower n ≤ fkRectAllSectorNormalization (R n) q)
    (hlowerCost : Tendsto (fun n =>
      -Real.log (lower n) / (R n).height) atTop (nhds 0)) :
    Tendsto (fun n =>
      -Real.log (fkRectAllSectorNormalization (R n) q) /
        (R n).height) atTop (nhds 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (f := fun n =>
      -Real.log (fkRectAllSectorNormalization (R n) q) /
        (R n).height)
    tendsto_const_nhds hlowerCost
  · filter_upwards [] with n
    apply div_nonneg
    · rw [neg_nonneg]
      exact Real.log_nonpos
        (fkRectAllSectorNormalization_pos (R n) hq).le
        (fkRectAllSectorNormalization_le_one (R n) hq)
    · positivity
  · filter_upwards [] with n
    apply div_le_div_of_nonneg_right
    · exact neg_le_neg (Real.log_le_log (hlowerPos n) (hlower n))
    · positivity



theorem tendsto_allSectorNormalization_negLog_div_height_zero_of_expectation
    (R : Nat → FKRectTorus) {q : Real} (hq : 4 < q)
    (L : Nat → Nat)
    (hmoment : ∀ n, fkRectCriticalZeroTurnExpectation (R n) q ≤
      ((L n + 1 : Nat) : Real) / 2)
    (hcost : Tendsto (fun n =>
      -Real.log ((2 / Real.sqrt q) ^ L n / (2 * q)) /
        (R n).height) atTop (nhds 0)) :
    Tendsto (fun n =>
      -Real.log (fkRectAllSectorNormalization (R n) q) /
        (R n).height) atTop (nhds 0) := by
  apply tendsto_allSectorNormalization_negLog_div_height_zero_of_lower
    R hq (fun n => (2 / Real.sqrt q) ^ L n / (2 * q))
  · intro n
    positivity
  · intro n
    exact zeroTurnCost_div_two_q_le_allSectorNormalization_of_expectation
      (R n) hq (L n) (hmoment n)
  · exact hcost



theorem tendsto_allSectorNormalization_negLog_div_height_zero_of_tail
    (R : Nat → FKRectTorus) {q : Real} (hq : 4 < q)
    (L : Nat → Nat)
    (htail : ∀ n, fkRectCriticalZeroTurnAboveMass (R n) q (L n) ≤
      (1 : Real) / 2)
    (hcost : Tendsto (fun n ↦
      -Real.log ((2 / Real.sqrt q) ^ L n / (2 * q)) /
        (R n).height) atTop (nhds 0)) :
    Tendsto (fun n ↦
      -Real.log (fkRectAllSectorNormalization (R n) q) /
        (R n).height) atTop (nhds 0) := by
  apply tendsto_allSectorNormalization_negLog_div_height_zero_of_lower
    R hq (fun n ↦ (2 / Real.sqrt q) ^ L n / (2 * q))
  · intro n
    positivity
  · intro n
    exact
      zeroTurnCost_div_two_q_le_allSectorNormalization_of_aboveMass_le_half
        (R n) hq (L n) (htail n)
  · exact hcost



theorem tendsto_allSectorNormalization_negLog_div_height_zero_of_sublinear_expectation
    (R : Nat → FKRectTorus) {q : Real} (hq : 4 < q)
    (L : Nat → Nat)
    (hmoment : ∀ n, fkRectCriticalZeroTurnExpectation (R n) q ≤
      ((L n + 1 : Nat) : Real) / 2)
    (hL : Tendsto (fun n => (L n : Real) / (R n).height)
      atTop (nhds 0))
    (hheight : Tendsto (fun n => (R n).height) atTop atTop) :
    Tendsto (fun n =>
      -Real.log (fkRectAllSectorNormalization (R n) q) /
        (R n).height) atTop (nhds 0) := by
  let a : Real := 2 / Real.sqrt q
  have hq0 : 0 < q := by linarith
  have ha : 0 < a := by dsimp [a]; positivity
  have htwoq : 0 < (2 : Real) * q := by positivity
  have hheightReal :
      Tendsto (fun n => ((R n).height : Real)) atTop atTop :=
    tendsto_natCast_atTop_iff.mpr hheight
  have hfirst : Tendsto (fun n =>
      -Real.log a * ((L n : Real) / (R n).height))
      atTop (nhds 0) := by
    simpa using hL.const_mul (-Real.log a)
  have hsecond : Tendsto (fun n =>
      Real.log (2 * q) / ((R n).height : Real))
      atTop (nhds 0) :=
    hheightReal.const_div_atTop (Real.log (2 * q))
  have hcost : Tendsto (fun n =>
      -Real.log (a ^ L n / (2 * q)) / (R n).height)
      atTop (nhds 0) := by
    have hadd := hfirst.add hsecond
    simpa only [zero_add] using hadd.congr' (by
      filter_upwards [] with n
      rw [Real.log_div (pow_ne_zero _ ha.ne') htwoq.ne', Real.log_pow]
      ring)
  apply tendsto_allSectorNormalization_negLog_div_height_zero_of_expectation
    R hq L hmoment
  simpa [a] using hcost


theorem tendsto_allSectorNormalization_negLog_div_height_zero_of_sublinear_tail
    (R : Nat → FKRectTorus) {q : Real} (hq : 4 < q)
    (L : Nat → Nat)
    (htail : ∀ n, fkRectCriticalZeroTurnAboveMass (R n) q (L n) ≤
      (1 : Real) / 2)
    (hL : Tendsto (fun n ↦ (L n : Real) / (R n).height)
      atTop (nhds 0))
    (hheight : Tendsto (fun n ↦ (R n).height) atTop atTop) :
    Tendsto (fun n ↦
      -Real.log (fkRectAllSectorNormalization (R n) q) /
        (R n).height) atTop (nhds 0) := by
  let a : Real := 2 / Real.sqrt q
  have hq0 : 0 < q := by linarith
  have ha : 0 < a := by dsimp [a]; positivity
  have htwoq : 0 < (2 : Real) * q := by positivity
  have hheightReal :
      Tendsto (fun n ↦ ((R n).height : Real)) atTop atTop :=
    tendsto_natCast_atTop_iff.mpr hheight
  have hfirst : Tendsto (fun n ↦
      -Real.log a * ((L n : Real) / (R n).height))
      atTop (nhds 0) := by
    simpa using hL.const_mul (-Real.log a)
  have hsecond : Tendsto (fun n ↦
      Real.log (2 * q) / ((R n).height : Real))
      atTop (nhds 0) :=
    hheightReal.const_div_atTop (Real.log (2 * q))
  have hcost : Tendsto (fun n ↦
      -Real.log (a ^ L n / (2 * q)) / (R n).height)
      atTop (nhds 0) := by
    have hadd := hfirst.add hsecond
    simpa only [zero_add] using hadd.congr' (by
      filter_upwards [] with n
      rw [Real.log_div (pow_ne_zero _ ha.ne') htwoq.ne', Real.log_pow]
      ring)
  apply tendsto_allSectorNormalization_negLog_div_height_zero_of_tail
    R hq L htail
  simpa [a] using hcost

end

end StatMech.FrontierD
