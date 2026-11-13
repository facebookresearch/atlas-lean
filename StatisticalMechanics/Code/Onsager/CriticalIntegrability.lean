/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Code.Onsager.CriticalTransfer









open scoped Real
open MeasureTheory Interval

namespace StatMech.Onsager

theorem ons_gInt_decompose (beta k1 k2 : ℝ) :
    ons_gInt beta k1 k2 =
      (Real.sinh (2 * beta) - 1) ^ 2 +
        Real.sinh (2 * beta) * (2 - Real.cos k1 - Real.cos k2) := by
  unfold ons_gInt
  have h := Real.cosh_sq_sub_sinh_sq (2 * beta)
  nlinarith

theorem ons_gInt_betaC (k1 k2 : ℝ) :
    ons_gInt ons_betaC k1 k2 = 2 - Real.cos k1 - Real.cos k2 := by
  rw [ons_gInt_decompose, ons_betaC_sinh]
  ring

noncomputable def ons_criticalLogBound (y : ℝ) : ℝ :=
  Real.log 9 + Real.log 2 + |Real.log (1 - Real.cos y)|

theorem ons_intervalIntegrable_criticalLogBound :
    IntervalIntegrable ons_criticalLogBound volume (-Real.pi) Real.pi := by
  have hmer : MeromorphicOn (fun y : ℝ => 1 - Real.cos y)
      [[-Real.pi, Real.pi]] :=
    (analyticOnNhd_const.sub Real.analyticOnNhd_cos).meromorphicOn
  have hlog : IntervalIntegrable (Real.log ∘ fun y : ℝ => 1 - Real.cos y)
      volume (-Real.pi) Real.pi := hmer.intervalIntegrable_log
  have habs : IntervalIntegrable (fun y : ℝ => |Real.log (1 - Real.cos y)|)
      volume (-Real.pi) Real.pi := by
    simpa only [Function.comp_apply, Real.norm_eq_abs] using hlog.norm
  have h9 : IntervalIntegrable (fun _y : ℝ => Real.log 9)
      volume (-Real.pi) Real.pi := intervalIntegrable_const
  have h2 : IntervalIntegrable (fun _y : ℝ => Real.log 2)
      volume (-Real.pi) Real.pi := intervalIntegrable_const
  exact (h9.add h2).add habs

theorem ons_criticalLogBound_nonneg (y : ℝ) :
    0 ≤ ons_criticalLogBound y := by
  unfold ons_criticalLogBound
  have h9 : 0 ≤ Real.log 9 := Real.log_nonneg (by norm_num)
  have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  positivity



theorem ons_log_gInt_bound
    (beta k1 k2 : ℝ)
    (hslo : (1 / 2 : ℝ) ≤ Real.sinh (2 * beta))
    (hshi : Real.sinh (2 * beta) ≤ 2)
    (hk2 : k2 ∈ Set.Icc (-Real.pi) Real.pi)
    (hk20 : k2 ≠ 0) :
    |Real.log (ons_gInt beta k1 k2)| ≤ ons_criticalLogBound k2 := by
  let s := Real.sinh (2 * beta)
  let a := 2 - Real.cos k1 - Real.cos k2
  let b := 1 - Real.cos k2
  have hbnonneg : 0 ≤ b := by
    dsimp [b]
    linarith [Real.cos_le_one k2]
  have hbpos : 0 < b := by
    apply lt_of_le_of_ne hbnonneg
    intro hbzero
    have hcos : Real.cos k2 = 1 := by dsimp [b] at hbzero; linarith
    have habs : |k2| ≤ Real.pi := by
      rw [abs_le]
      exact hk2
    have hz : k2 = 0 := by
      exact (Real.cos_eq_one_iff_of_lt_of_lt
        (by rw [abs_le] at habs; linarith [Real.pi_pos])
        (by rw [abs_le] at habs; linarith [Real.pi_pos])).mp hcos
    exact hk20 hz
  have hab : b ≤ a := by
    dsimp [a, b]
    linarith [Real.cos_le_one k1]
  have hsnonneg : 0 ≤ s := le_trans (by norm_num) hslo
  have hsone : |s - 1| ≤ 1 := by
    rw [abs_le]
    constructor <;> dsimp [s] at * <;> linarith
  have hgform : ons_gInt beta k1 k2 = (s - 1) ^ 2 + s * a :=
    ons_gInt_decompose beta k1 k2
  have hglower : b / 2 ≤ ons_gInt beta k1 k2 := by
    rw [hgform]
    have hsa : b / 2 ≤ s * a := by
      calc
        b / 2 = (1 / 2 : ℝ) * b := by ring
        _ ≤ s * b := mul_le_mul_of_nonneg_right hslo hbnonneg
        _ ≤ s * a := mul_le_mul_of_nonneg_left hab hsnonneg
    nlinarith [sq_nonneg (s - 1)]
  have hgupper : ons_gInt beta k1 k2 ≤ 9 := by
    rw [hgform]
    have ha4 : a ≤ 4 := by
      dsimp [a]
      nlinarith [Real.neg_one_le_cos k1, Real.neg_one_le_cos k2]
    have hsquare : (s - 1) ^ 2 ≤ 1 := by
      nlinarith [sq_nonneg (s - 1), hsone]
    nlinarith
  have hgpos : 0 < ons_gInt beta k1 k2 :=
    lt_of_lt_of_le (half_pos hbpos) hglower
  have hlogupper : Real.log (ons_gInt beta k1 k2) ≤ Real.log 9 :=
    Real.log_le_log hgpos hgupper
  have hloglower : Real.log b - Real.log 2 ≤
      Real.log (ons_gInt beta k1 k2) := by
    have hhalfpos : 0 < b / 2 := half_pos hbpos
    have hlog := Real.log_le_log hhalfpos hglower
    rw [Real.log_div hbpos.ne' (by norm_num : (2 : ℝ) ≠ 0)] at hlog
    exact hlog
  rw [abs_le]
  constructor
  · unfold ons_criticalLogBound
    have hlogabs : -|Real.log b| ≤ Real.log b := neg_abs_le _
    have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hlog9 : 0 ≤ Real.log 9 := Real.log_nonneg (by norm_num)
    linarith
  · unfold ons_criticalLogBound
    have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have habs : 0 ≤ |Real.log b| := abs_nonneg _
    exact hlogupper.trans (by linarith)

theorem ons_eventually_sinh_bounds :
    ∀ᶠ beta : ℝ in nhds ons_betaC,
      (1 / 2 : ℝ) ≤ Real.sinh (2 * beta) ∧
        Real.sinh (2 * beta) ≤ 2 := by
  have ht : Filter.Tendsto (fun beta : ℝ => Real.sinh (2 * beta))
      (nhds ons_betaC) (nhds 1) := by
    have hc : ContinuousAt (fun beta : ℝ => Real.sinh (2 * beta))
        ons_betaC := by
      fun_prop
    simpa only [ons_betaC_sinh] using hc.tendsto
  have hev : ∀ᶠ beta : ℝ in nhds ons_betaC,
      dist (Real.sinh (2 * beta)) 1 < 1 / 2 :=
    ht (Metric.ball_mem_nhds 1 (by norm_num))
  filter_upwards [hev] with beta hbeta
  rw [Real.dist_eq, abs_lt] at hbeta
  constructor <;> linarith



theorem ons_inner_integral_tendsto_betaC (k1 : ℝ) :
    Filter.Tendsto
      (fun beta : ℝ => ∫ k2 in (-Real.pi)..Real.pi,
        Real.log (ons_gInt beta k1 k2))
      (nhds ons_betaC)
      (nhds (∫ k2 in (-Real.pi)..Real.pi,
        Real.log (ons_gInt ons_betaC k1 k2))) := by
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    ons_criticalLogBound
  · filter_upwards [] with beta
    apply Measurable.aestronglyMeasurable
    apply Real.measurable_log.comp
    unfold ons_gInt
    fun_prop
  · filter_upwards [ons_eventually_sinh_bounds] with beta hbeta
    filter_upwards [MeasureTheory.volume.ae_ne (0 : ℝ)] with k2 hk20 hk2
    rw [Real.norm_eq_abs]
    have hk2' := Set.uIoc_subset_uIcc hk2
    rw [Set.uIcc_of_le (by linarith [Real.pi_pos])] at hk2'
    exact ons_log_gInt_bound beta k1 k2 hbeta.1 hbeta.2 hk2' hk20
  · exact ons_intervalIntegrable_criticalLogBound
  · filter_upwards [MeasureTheory.volume.ae_ne (0 : ℝ)] with k2 hk20 hk2
    have hbpos : 0 < 1 - Real.cos k2 := by
      have hbnonneg : 0 ≤ 1 - Real.cos k2 := by
        linarith [Real.cos_le_one k2]
      apply lt_of_le_of_ne hbnonneg
      intro hbzero
      have hcos : Real.cos k2 = 1 := by linarith
      have hk2mem := Set.uIoc_subset_uIcc hk2
      rw [Set.uIcc_of_le (by linarith [Real.pi_pos])] at hk2mem
      have habs : |k2| ≤ Real.pi := by
        rw [abs_le]
        exact hk2mem
      have hz : k2 = 0 :=
        (Real.cos_eq_one_iff_of_lt_of_lt
          (by rw [abs_le] at habs; linarith [Real.pi_pos])
          (by rw [abs_le] at habs; linarith [Real.pi_pos])).mp hcos
      exact hk20 hz
    have hgpos : 0 < ons_gInt ons_betaC k1 k2 := by
      rw [ons_gInt_betaC]
      have hc : Real.cos k1 ≤ 1 := Real.cos_le_one k1
      linarith
    have hc : ContinuousAt (fun beta : ℝ => ons_gInt beta k1 k2)
        ons_betaC := by
      unfold ons_gInt
      fun_prop
    exact (hc.log hgpos.ne').tendsto

private theorem ons_one_sub_cos_pos_Icc {k : ℝ}
    (hk : k ∈ Set.Icc (-Real.pi) Real.pi) (hk0 : k ≠ 0) :
    0 < 1 - Real.cos k := by
  have hbnonneg : 0 ≤ 1 - Real.cos k := by
    linarith [Real.cos_le_one k]
  apply lt_of_le_of_ne hbnonneg
  intro hbzero
  have hcos : Real.cos k = 1 := by linarith
  have habs : |k| ≤ Real.pi := by
    rw [abs_le]
    exact hk
  have hz : k = 0 :=
    (Real.cos_eq_one_iff_of_lt_of_lt
      (by rw [abs_le] at habs; linarith [Real.pi_pos])
      (by rw [abs_le] at habs; linarith [Real.pi_pos])).mp hcos
  exact hk0 hz

theorem ons_inner_integral_continuous_near_betaC (beta : ℝ)
    (hslo : (1 / 2 : ℝ) ≤ Real.sinh (2 * beta))
    (hshi : Real.sinh (2 * beta) ≤ 2) :
    Continuous (fun k1 : ℝ => ∫ k2 in (-Real.pi)..Real.pi,
      Real.log (ons_gInt beta k1 k2)) := by
  rw [continuous_iff_continuousAt]
  intro k1
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    ons_criticalLogBound
  · filter_upwards [] with k1'
    apply Measurable.aestronglyMeasurable
    apply Real.measurable_log.comp
    unfold ons_gInt
    fun_prop
  · filter_upwards [] with k1'
    filter_upwards [MeasureTheory.volume.ae_ne (0 : ℝ)] with k2 hk20 hk2
    rw [Real.norm_eq_abs]
    have hk2' := Set.uIoc_subset_uIcc hk2
    rw [Set.uIcc_of_le (by linarith [Real.pi_pos])] at hk2'
    exact ons_log_gInt_bound beta k1' k2 hslo hshi hk2' hk20
  · exact ons_intervalIntegrable_criticalLogBound
  · filter_upwards [MeasureTheory.volume.ae_ne (0 : ℝ)] with k2 hk20 hk2
    have hk2' := Set.uIoc_subset_uIcc hk2
    rw [Set.uIcc_of_le (by linarith [Real.pi_pos])] at hk2'
    have hbpos := ons_one_sub_cos_pos_Icc hk2' hk20
    have hgpos : 0 < ons_gInt beta k1 k2 := by
      rw [ons_gInt_decompose]
      have hab : 1 - Real.cos k2 ≤
          2 - Real.cos k1 - Real.cos k2 := by
        linarith [Real.cos_le_one k1]
      have hsnonneg : 0 ≤ Real.sinh (2 * beta) := by linarith
      have hprod : 0 < Real.sinh (2 * beta) *
          (2 - Real.cos k1 - Real.cos k2) :=
        mul_pos (lt_of_lt_of_le (by norm_num) hslo)
          (lt_of_lt_of_le hbpos hab)
      nlinarith [sq_nonneg (Real.sinh (2 * beta) - 1)]
    have hc : ContinuousAt (fun k1' : ℝ => ons_gInt beta k1' k2) k1 := by
      unfold ons_gInt
      fun_prop
    exact (hc.log hgpos.ne').tendsto

noncomputable def ons_criticalInnerBound : ℝ :=
  |∫ k2 in (-Real.pi)..Real.pi, ons_criticalLogBound k2|

theorem ons_inner_integral_norm_le (beta k1 : ℝ)
    (hslo : (1 / 2 : ℝ) ≤ Real.sinh (2 * beta))
    (hshi : Real.sinh (2 * beta) ≤ 2) :
    ‖∫ k2 in (-Real.pi)..Real.pi, Real.log (ons_gInt beta k1 k2)‖ ≤
      ons_criticalInnerBound := by
  unfold ons_criticalInnerBound
  apply intervalIntegral.norm_integral_le_abs_of_norm_le
  · rw [ae_restrict_iff' measurableSet_uIoc]
    filter_upwards [MeasureTheory.volume.ae_ne (0 : ℝ)] with k2 hk20 hk2
    rw [Real.norm_eq_abs]
    have hk2' := Set.uIoc_subset_uIcc hk2
    rw [Set.uIcc_of_le (by linarith [Real.pi_pos])] at hk2'
    exact ons_log_gInt_bound beta k1 k2 hslo hshi hk2' hk20
  · exact ons_intervalIntegrable_criticalLogBound

theorem ons_double_integral_tendsto_betaC :
    Filter.Tendsto
      (fun beta : ℝ => ∫ k1 in (-Real.pi)..Real.pi,
        ∫ k2 in (-Real.pi)..Real.pi, Real.log (ons_gInt beta k1 k2))
      (nhds ons_betaC)
      (nhds (∫ k1 in (-Real.pi)..Real.pi,
        ∫ k2 in (-Real.pi)..Real.pi,
          Real.log (ons_gInt ons_betaC k1 k2))) := by
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun _k1 : ℝ => ons_criticalInnerBound)
  · filter_upwards [ons_eventually_sinh_bounds] with beta hbeta
    exact (ons_inner_integral_continuous_near_betaC
      beta hbeta.1 hbeta.2).aestronglyMeasurable
  · filter_upwards [ons_eventually_sinh_bounds] with beta hbeta
    filter_upwards [] with k1 hk1
    exact ons_inner_integral_norm_le beta k1 hbeta.1 hbeta.2
  · exact intervalIntegrable_const
  · filter_upwards [] with k1 hk1
    exact ons_inner_integral_tendsto_betaC k1

theorem ons_continuousAt_freeEnergyIntegral_betaC :
    ContinuousAt ons_freeEnergyIntegral ons_betaC := by
  unfold ons_freeEnergyIntegral
  exact (ons_double_integral_tendsto_betaC.const_mul
    (1 / (8 * Real.pi ^ 2)))



theorem ons_continuousAt_pressure_betaC :
    ContinuousAt ons_pressure ons_betaC := by
  unfold ons_pressure
  exact continuousAt_const.add ons_continuousAt_freeEnergyIntegral_betaC

end StatMech.Onsager
