/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectMedialDualShift
import Code.FrontierD.FKRectEulerNetIdentification
import Code.FrontierD.FKRectRandomClusterEventFKG



namespace StatMech.FrontierD

noncomputable section



theorem fkRectMedialLoopCount_dual
    (R : FKRectTorus) (omega : R.Configuration) :
    fkRectMedialLoopCount R (fkRectDualConfigurationEquiv R omega) =
      fkRectMedialLoopCount R omega := by
  unfold fkRectMedialLoopCount fkMedialLoopCount
  exact (Nat.card_congr
    (fkRectMedialDualShiftGraphIso R omega).connectedComponentEquiv).symm


theorem fkRectCriticalReducedWeight_eq_loop_net
    (R : FKRectTorus) {q : Real} (hq : 0 < q)
    (omega : R.Configuration) :
    fkRectCriticalReducedWeight R q omega =
      Real.sqrt q ^ (R.width * R.height : Nat) *
        Real.sqrt q ^ fkRectMedialLoopCount R omega *
          q ^ fkRectNetIndicator R omega := by
  rw [fkRectCriticalReducedWeight_eq_loop_defect R hq,
    fkRectEulerHomologyDefect_eq_two_mul_netIndicator_configuration]
  let s := fkRectNetIndicator R omega
  rw [show 2 * (s : Int) = (2 * s : Nat) by omega, zpow_natCast]
  change _ * _ * Real.sqrt q ^ (2 * s) = _ * _ * q ^ s
  have hpow : Real.sqrt q ^ (2 * s) = q ^ s := by
    calc
      Real.sqrt q ^ (2 * s) = (Real.sqrt q ^ 2) ^ s :=
        pow_mul (Real.sqrt q) 2 s
      _ = q ^ s := by rw [Real.sq_sqrt hq.le]
  rw [hpow]



theorem fkRectCriticalReducedWeight_dual_le
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q)
    (omega : R.Configuration) :
    fkRectCriticalReducedWeight R q
        (fkRectDualConfigurationEquiv R omega) ≤
      q * fkRectCriticalReducedWeight R q omega := by
  rw [fkRectCriticalReducedWeight_eq_loop_net R (zero_lt_one.trans_le hq),
    fkRectCriticalReducedWeight_eq_loop_net R (zero_lt_one.trans_le hq),
    fkRectMedialLoopCount_dual]
  let B := Real.sqrt q ^ (R.width * R.height : Nat) *
    Real.sqrt q ^ fkRectMedialLoopCount R omega
  let s := fkRectNetIndicator R omega
  let t := fkRectNetIndicator R (fkRectDualConfigurationEquiv R omega)
  change B * q ^ t ≤ q * (B * q ^ s)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hs : s ≤ 1 := fkRectNetIndicator_le_one R omega
  have ht : t ≤ 1 := fkRectNetIndicator_le_one R
    (fkRectDualConfigurationEquiv R omega)
  have hq0 : 0 ≤ q := zero_le_one.trans hq
  have hq2 : 1 ≤ q * q := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hq) (add_nonneg hq0 zero_le_one)]
  have hBq : 0 ≤ B * q := mul_nonneg hB hq0
  interval_cases s <;> interval_cases t <;> norm_num <;>
    nlinarith [mul_nonneg hB (sub_nonneg.mpr hq),
      mul_nonneg hB (sub_nonneg.mpr hq2),
      mul_nonneg hBq (sub_nonneg.mpr hq)]



theorem fkRectCriticalReducedWeight_le_q_mul_dual
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q)
    (omega : R.Configuration) :
    fkRectCriticalReducedWeight R q omega ≤
      q * fkRectCriticalReducedWeight R q
        (fkRectDualConfigurationEquiv R omega) := by
  rw [fkRectCriticalReducedWeight_eq_loop_net R (zero_lt_one.trans_le hq),
    fkRectCriticalReducedWeight_eq_loop_net R (zero_lt_one.trans_le hq),
    fkRectMedialLoopCount_dual]
  let B := Real.sqrt q ^ (R.width * R.height : Nat) *
    Real.sqrt q ^ fkRectMedialLoopCount R omega
  let s := fkRectNetIndicator R omega
  let t := fkRectNetIndicator R (fkRectDualConfigurationEquiv R omega)
  change B * q ^ s ≤ q * (B * q ^ t)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hs : s ≤ 1 := fkRectNetIndicator_le_one R omega
  have ht : t ≤ 1 := fkRectNetIndicator_le_one R
    (fkRectDualConfigurationEquiv R omega)
  have hq0 : 0 ≤ q := zero_le_one.trans hq
  have hq2 : 1 ≤ q * q := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hq) (add_nonneg hq0 zero_le_one)]
  have hBq : 0 ≤ B * q := mul_nonneg hB hq0
  interval_cases s <;> interval_cases t <;> norm_num <;>
    nlinarith [mul_nonneg hB (sub_nonneg.mpr hq),
      mul_nonneg hB (sub_nonneg.mpr hq2),
      mul_nonneg hBq (sub_nonneg.mpr hq)]


theorem fkRectCriticalRandomClusterProb_dual_le
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q)
    (omega : R.Configuration) :
    fkRectCriticalRandomClusterProb R q
        (fkRectDualConfigurationEquiv R omega) ≤
      q * fkRectCriticalRandomClusterProb R q omega := by
  unfold fkRectCriticalRandomClusterProb
  rw [show q *
      (fkRectCriticalReducedWeight R q omega /
        fkRectCriticalReducedZ R q) =
      (q * fkRectCriticalReducedWeight R q omega) /
        fkRectCriticalReducedZ R q by ring]
  exact div_le_div_of_nonneg_right
    (fkRectCriticalReducedWeight_dual_le R hq omega)
    (fkRectCriticalReducedZ_pos R (zero_lt_one.trans_le hq)).le

theorem fkRectCriticalRandomClusterProb_le_q_mul_dual
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q)
    (omega : R.Configuration) :
    fkRectCriticalRandomClusterProb R q omega ≤
      q * fkRectCriticalRandomClusterProb R q
        (fkRectDualConfigurationEquiv R omega) := by
  unfold fkRectCriticalRandomClusterProb
  rw [show q *
      (fkRectCriticalReducedWeight R q
          (fkRectDualConfigurationEquiv R omega) /
        fkRectCriticalReducedZ R q) =
      (q * fkRectCriticalReducedWeight R q
          (fkRectDualConfigurationEquiv R omega)) /
        fkRectCriticalReducedZ R q by ring]
  exact div_le_div_of_nonneg_right
    (fkRectCriticalReducedWeight_le_q_mul_dual R hq omega)
    (fkRectCriticalReducedZ_pos R (zero_lt_one.trans_le hq)).le


def fkRectDualEvent (R : FKRectTorus)
    (A : Set R.Configuration) : Set R.Configuration :=
  fkRectDualConfigurationEquiv R '' A


def fkRectDualPreimageEvent (R : FKRectTorus)
    (A : Set R.Configuration) : Set R.Configuration :=
  fkRectDualConfigurationEquiv R ⁻¹' A

theorem fkRectDualPreimageEvent_isIncreasing
    (R : FKRectTorus) {A : Set R.Configuration} (hA : IsDecreasing A) :
    IsIncreasing (fkRectDualPreimageEvent R A) := by
  intro omega tau hot homega
  exact hA (fkRectDualConfigurationEquiv_antitone R hot) homega

theorem fkRectDualEvent_dualPreimageEvent
    (R : FKRectTorus) (A : Set R.Configuration) :
    fkRectDualEvent R (fkRectDualPreimageEvent R A) = A := by
  ext eta
  constructor
  · rintro ⟨omega, homega, rfl⟩
    exact homega
  · intro heta
    exact ⟨(fkRectDualConfigurationEquiv R).symm eta, by
      simpa [fkRectDualPreimageEvent] using heta,
      (fkRectDualConfigurationEquiv R).apply_symm_apply eta⟩



theorem fkRectCriticalEventMass_dualEvent_eq
    (R : FKRectTorus) (q : Real) (A : Set R.Configuration) :
    fkRectCriticalEventMass R q (fkRectDualEvent R A) =
      ∑ omega : R.Configuration,
        A.indicator (fun omega =>
          fkRectCriticalRandomClusterProb R q
            (fkRectDualConfigurationEquiv R omega)) omega := by
  classical
  unfold fkRectCriticalEventMass
  apply Fintype.sum_equiv (fkRectDualConfigurationEquiv R).symm
  intro eta
  by_cases hA : (fkRectDualConfigurationEquiv R).symm eta ∈ A
  · have hdual : eta ∈ fkRectDualEvent R A := by
      exact ⟨(fkRectDualConfigurationEquiv R).symm eta, hA,
        (fkRectDualConfigurationEquiv R).apply_symm_apply eta⟩
    rw [Set.indicator_of_mem hdual, Set.indicator_of_mem hA]
    simp
  · have hdual : eta ∉ fkRectDualEvent R A := by
      rintro ⟨omega, homega, rfl⟩
      exact hA (by simpa using homega)
    rw [Set.indicator_of_notMem hdual, Set.indicator_of_notMem hA]


theorem fkRectCriticalEventMass_dualEvent_le
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q)
    (A : Set R.Configuration) :
    fkRectCriticalEventMass R q (fkRectDualEvent R A) ≤
      q * fkRectCriticalEventMass R q A := by
  rw [fkRectCriticalEventMass_dualEvent_eq,
    fkRectCriticalEventMass_eq_indicatorExpectation, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro omega homega
  by_cases hA : omega ∈ A
  · rw [Set.indicator_of_mem hA, Set.indicator_of_mem hA]
    simpa using fkRectCriticalRandomClusterProb_dual_le R hq omega
  · simp [Set.indicator_of_notMem hA]

theorem fkRectCriticalEventMass_le_q_mul_dualEvent
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q)
    (A : Set R.Configuration) :
    fkRectCriticalEventMass R q A ≤
      q * fkRectCriticalEventMass R q (fkRectDualEvent R A) := by
  rw [fkRectCriticalEventMass_dualEvent_eq,
    fkRectCriticalEventMass_eq_indicatorExpectation, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro omega homega
  by_cases hA : omega ∈ A
  · rw [Set.indicator_of_mem hA, Set.indicator_of_mem hA]
    simpa using fkRectCriticalRandomClusterProb_le_q_mul_dual R hq omega
  · simp [Set.indicator_of_notMem hA]




theorem one_div_q_mul_eventMass_le_of_dualEvent_subset
    (R : FKRectTorus) {q : Real} (hq : 1 <= q)
    {A B : Set R.Configuration} (hAB : fkRectDualEvent R A ⊆ B) :
    (1 / q) * fkRectCriticalEventMass R q A <=
      fkRectCriticalEventMass R q B := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hdual := fkRectCriticalEventMass_le_q_mul_dualEvent R hq A
  have hmono := fkRectCriticalEventMass_mono R hq0 hAB
  rw [one_div, inv_mul_eq_div, div_le_iff₀ hq0]
  exact hdual.trans (by
    simpa [mul_comm] using mul_le_mul_of_nonneg_left hmono hq0.le)



theorem one_div_one_add_q_le_eventMass_of_compl_subset_dualEvent
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q)
    (A : Set R.Configuration) (hcover : Aᶜ ⊆ fkRectDualEvent R A) :
    1 / (1 + q) ≤ fkRectCriticalEventMass R q A := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hmono := fkRectCriticalEventMass_mono R hq0 hcover
  have hdual := fkRectCriticalEventMass_dualEvent_le R hq A
  rw [fkRectCriticalEventMass_compl R hq0 A] at hmono
  have hbasic : 1 - fkRectCriticalEventMass R q A ≤
      q * fkRectCriticalEventMass R q A := hmono.trans hdual
  have hden : 0 < 1 + q := by linarith
  rw [div_le_iff₀ hden]
  nlinarith




theorem one_div_one_add_q_le_eventMass_of_dualCompl_subset
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q)
    (A : Set R.Configuration)
    (hcover : fkRectDualEvent R Aᶜ ⊆ A) :
    1 / (1 + q) ≤ fkRectCriticalEventMass R q A := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hdual := fkRectCriticalEventMass_le_q_mul_dualEvent R hq Aᶜ
  have hmono := fkRectCriticalEventMass_mono R hq0 hcover
  rw [fkRectCriticalEventMass_compl R hq0 A] at hdual
  have hbasic : 1 - fkRectCriticalEventMass R q A ≤
      q * fkRectCriticalEventMass R q A :=
    hdual.trans (mul_le_mul_of_nonneg_left hmono (zero_le_one.trans hq))
  have hden : 0 < 1 + q := by linarith
  rw [div_le_iff₀ hden]
  nlinarith

end

end StatMech.FrontierD
