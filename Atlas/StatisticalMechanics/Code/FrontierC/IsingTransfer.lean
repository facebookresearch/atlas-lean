/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Onsager.DetLoopExpansion
import Code.Onsager.TracePowWalk
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Order.Filter.AtTopBot.Basic











open scoped BigOperators
open Matrix Polynomial

namespace StatMech.FrontierC



noncomputable def isingTransferReal (beta h : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.exp (beta + h), Real.exp (-beta);
     Real.exp (-beta), Real.exp (beta - h)]



noncomputable def isingTransfer (beta h : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (isingTransferReal beta h).map (algebraMap ℝ ℂ)

private noncomputable def transferA (beta h : ℝ) : ℝ := Real.exp (beta + h)
private noncomputable def transferB (beta : ℝ) : ℝ := Real.exp (-beta)
private noncomputable def transferD (beta h : ℝ) : ℝ := Real.exp (beta - h)


noncomputable def isingTransferDisc (beta h : ℝ) : ℝ :=
  Real.sqrt ((transferA beta h - transferD beta h) ^ 2 +
    4 * transferB beta ^ 2)


noncomputable def isingTransferEigenPlus (beta h : ℝ) : ℝ :=
  (transferA beta h + transferD beta h + isingTransferDisc beta h) / 2


noncomputable def isingTransferEigenMinus (beta h : ℝ) : ℝ :=
  (transferA beta h + transferD beta h - isingTransferDisc beta h) / 2

lemma isingTransfer_disc_sq (beta h : ℝ) :
    isingTransferDisc beta h ^ 2 =
      (transferA beta h - transferD beta h) ^ 2 +
        4 * transferB beta ^ 2 := by
  rw [isingTransferDisc, Real.sq_sqrt]
  positivity

lemma isingTransfer_eigen_sum (beta h : ℝ) :
    isingTransferEigenPlus beta h + isingTransferEigenMinus beta h =
      transferA beta h + transferD beta h := by
  simp only [isingTransferEigenPlus, isingTransferEigenMinus]
  ring

lemma isingTransfer_eigen_prod (beta h : ℝ) :
    isingTransferEigenPlus beta h * isingTransferEigenMinus beta h =
      transferA beta h * transferD beta h - transferB beta ^ 2 := by
  have hs := isingTransfer_disc_sq beta h
  simp only [isingTransferEigenPlus, isingTransferEigenMinus]
  nlinarith

lemma isingTransfer_disc_pos (beta h : ℝ) : 0 < isingTransferDisc beta h := by
  rw [isingTransferDisc]
  apply Real.sqrt_pos.2
  have hb : 0 < transferB beta := Real.exp_pos _
  nlinarith [sq_nonneg (transferA beta h - transferD beta h)]

lemma isingTransfer_eigenPlus_pos (beta h : ℝ) :
    0 < isingTransferEigenPlus beta h := by
  have ha : 0 < transferA beta h := Real.exp_pos _
  have hd : 0 < transferD beta h := Real.exp_pos _
  have hs := isingTransfer_disc_pos beta h
  rw [isingTransferEigenPlus]
  positivity

lemma isingTransfer_trace (beta h : ℝ) :
    (isingTransfer beta h).trace =
      ((transferA beta h + transferD beta h : ℝ) : ℂ) := by
  simp [isingTransfer, isingTransferReal, Matrix.trace_fin_two,
    transferA, transferD]

lemma isingTransfer_det (beta h : ℝ) :
    (isingTransfer beta h).det =
      ((transferA beta h * transferD beta h - transferB beta ^ 2 : ℝ) : ℂ) := by
  simp [isingTransfer, isingTransferReal, Matrix.det_fin_two,
    transferA, transferB, transferD]
  ring_nf


theorem isingTransfer_charpoly (beta h : ℝ) :
    (isingTransfer beta h).charpoly =
      (X - C (isingTransferEigenPlus beta h : ℂ)) *
      (X - C (isingTransferEigenMinus beta h : ℂ)) := by
  rw [Matrix.charpoly_fin_two, isingTransfer_trace, isingTransfer_det]
  rw [← isingTransfer_eigen_sum beta h, ← isingTransfer_eigen_prod beta h]
  push_cast
  simp only [map_add, map_mul]
  ring

lemma isingTransfer_roots (beta h : ℝ) :
    (isingTransfer beta h).charpoly.roots =
      {(isingTransferEigenPlus beta h : ℂ),
       (isingTransferEigenMinus beta h : ℂ)} := by
  rw [isingTransfer_charpoly, roots_mul]
  · simp [roots_X_sub_C]
  · exact mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)




theorem isingTransfer_trace_pow (beta h : ℝ) (n : ℕ) :
    ((isingTransfer beta h) ^ n).trace =
      (isingTransferEigenPlus beta h : ℂ) ^ n +
      (isingTransferEigenMinus beta h : ℂ) ^ n := by
  have htoLin_pow : ((isingTransfer beta h) ^ n).toLin' =
      (isingTransfer beta h).toLin' ^ n := by
    induction n with
    | zero => simp [Matrix.toLin'_one, Module.End.one_eq_id]
    | succ n ih =>
        rw [pow_succ, Matrix.toLin'_mul, ih, pow_succ, Module.End.mul_eq_comp]
  rw [← Matrix.trace_toLin'_eq, htoLin_pow,
    StatMech.Onsager.trace_pow_endo, Matrix.charpoly_toLin',
    isingTransfer_roots]
  simp


def transferSpin (s : Fin 2) : ℝ := if s = 0 then 1 else -1

@[simp] lemma transferSpin_zero : transferSpin 0 = 1 := by simp [transferSpin]
@[simp] lemma transferSpin_one : transferSpin 1 = -1 := by simp [transferSpin]



noncomputable def isingRingExponent {n : ℕ} [NeZero n]
    (beta h : ℝ) (s : Fin n → Fin 2) : ℝ :=
  (∑ k : Fin n, beta * transferSpin (s k) * transferSpin (s (k + 1))) +
    h * ∑ k : Fin n, transferSpin (s k)



noncomputable def isingRingZ (n : ℕ) [NeZero n] (beta h : ℝ) : ℝ :=
  ∑ s : Fin n → Fin 2, Real.exp (isingRingExponent beta h s)

lemma isingTransfer_apply (beta h : ℝ) (s t : Fin 2) :
    isingTransfer beta h s t =
      (Real.exp (beta * transferSpin s * transferSpin t +
        (h / 2) * (transferSpin s + transferSpin t)) : ℂ) := by
  fin_cases s <;> fin_cases t <;>
    simp [isingTransfer, isingTransferReal, transferSpin] <;>
    congr 2 <;> ring

lemma sum_transferSpin_add_one {n : ℕ} [NeZero n] (s : Fin n → Fin 2) :
    (∑ k : Fin n, transferSpin (s (k + 1))) =
      ∑ k : Fin n, transferSpin (s k) := by
  exact Equiv.sum_comp (Equiv.addRight (1 : Fin n))
    (fun k => transferSpin (s k))

lemma isingTransfer_loopWeight {n : ℕ} [NeZero n]
    (beta h : ℝ) (s : Fin n → Fin 2) :
    (∏ k : Fin n, isingTransfer beta h (s k) (s (k + 1))) =
      (Real.exp (isingRingExponent beta h s) : ℂ) := by
  simp_rw [isingTransfer_apply]
  change (∏ k : Fin n, algebraMap ℝ ℂ
      (Real.exp (beta * transferSpin (s k) * transferSpin (s (k + 1)) +
        (h / 2) * (transferSpin (s k) + transferSpin (s (k + 1)))))) =
    algebraMap ℝ ℂ (Real.exp (isingRingExponent beta h s))
  rw [← map_prod, ← Real.exp_sum]
  congr 2
  rw [isingRingExponent, Finset.sum_add_distrib]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    sum_transferSpin_add_one]
  ring



theorem isingRingZ_eq_trace (n : ℕ) [NeZero n] (hn : 0 < n) (beta h : ℝ) :
    (isingRingZ n beta h : ℂ) = ((isingTransfer beta h) ^ n).trace := by
  rw [StatMech.Onsager.ons_trace_pow_eq_walk_sum _ n hn]
  rw [isingRingZ]
  change algebraMap ℝ ℂ (∑ s : Fin n → Fin 2,
      Real.exp (isingRingExponent beta h s)) = _
  rw [map_sum]
  exact Finset.sum_congr rfl (fun s _ => (isingTransfer_loopWeight beta h s).symm)



theorem isingRingZ_eigenvalues (n : ℕ) [NeZero n] (hn : 0 < n) (beta h : ℝ) :
    (isingRingZ n beta h : ℂ) =
      (isingTransferEigenPlus beta h : ℂ) ^ n +
      (isingTransferEigenMinus beta h : ℂ) ^ n := by
  rw [isingRingZ_eq_trace n hn, isingTransfer_trace_pow]


theorem isingRingZ_eigenvalues_real (n : ℕ) [NeZero n] (hn : 0 < n)
    (beta h : ℝ) :
    isingRingZ n beta h =
      isingTransferEigenPlus beta h ^ n +
      isingTransferEigenMinus beta h ^ n := by
  exact_mod_cast isingRingZ_eigenvalues n hn beta h

lemma isingRingZ_pos (n : ℕ) [NeZero n] (beta h : ℝ) :
    0 < isingRingZ n beta h := by
  unfold isingRingZ
  exact Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty


lemma isingTransfer_abs_eigenMinus_lt (beta h : ℝ) :
    |isingTransferEigenMinus beta h| < isingTransferEigenPlus beta h := by
  have hs : 0 < transferA beta h + transferD beta h :=
    add_pos (Real.exp_pos _) (Real.exp_pos _)
  have hd := isingTransfer_disc_pos beta h
  rw [abs_lt]
  simp only [isingTransferEigenPlus, isingTransferEigenMinus]
  constructor <;> linarith

lemma isingTransfer_eigenRatio_abs_lt_one (beta h : ℝ) :
    |isingTransferEigenMinus beta h / isingTransferEigenPlus beta h| < 1 := by
  rw [abs_div, abs_of_pos (isingTransfer_eigenPlus_pos beta h),
    div_lt_one (isingTransfer_eigenPlus_pos beta h)]
  exact isingTransfer_abs_eigenMinus_lt beta h

private lemma isingRing_spectral_factor (beta h : ℝ) (n : ℕ) :
    isingTransferEigenPlus beta h ^ n + isingTransferEigenMinus beta h ^ n =
      isingTransferEigenPlus beta h ^ n *
        (1 + (isingTransferEigenMinus beta h /
          isingTransferEigenPlus beta h) ^ n) := by
  have hp : isingTransferEigenPlus beta h ≠ 0 :=
    (isingTransfer_eigenPlus_pos beta h).ne'
  rw [div_pow]
  field_simp [pow_ne_zero _ hp]

private lemma isingRing_ratio_factor_pos (beta h : ℝ) (n : ℕ) :
    0 < 1 + (isingTransferEigenMinus beta h /
      isingTransferEigenPlus beta h) ^ (n + 1) := by
  let r := isingTransferEigenMinus beta h / isingTransferEigenPlus beta h
  have hr : |r| < 1 := isingTransfer_eigenRatio_abs_lt_one beta h
  have hrpow : |r ^ (n + 1)| < 1 := by
    rw [abs_pow]
    exact pow_lt_one₀ (abs_nonneg r) hr (by omega)
  rw [abs_lt] at hrpow
  linarith



theorem isingRing_pressure_tendsto (beta h : ℝ) :
    Filter.Tendsto
      (fun n : ℕ => Real.log (isingRingZ (n + 1) beta h) / (n + 1 : ℝ))
      Filter.atTop
      (nhds (Real.log (isingTransferEigenPlus beta h))) := by
  let r := isingTransferEigenMinus beta h / isingTransferEigenPlus beta h
  have hr : |r| < 1 := isingTransfer_eigenRatio_abs_lt_one beta h
  have hshift : Filter.Tendsto (fun n : ℕ => n + 1) Filter.atTop Filter.atTop := by
    rw [Filter.tendsto_atTop]
    intro b
    filter_upwards [Filter.eventually_ge_atTop b] with n hn
    omega
  have hrpow : Filter.Tendsto (fun n : ℕ => r ^ (n + 1)) Filter.atTop (nhds 0) :=
    (tendsto_pow_atTop_nhds_zero_of_abs_lt_one hr).comp hshift
  have hlog : Filter.Tendsto (fun n : ℕ => Real.log (1 + r ^ (n + 1)))
      Filter.atTop (nhds 0) := by
    convert (tendsto_const_nhds.add hrpow).log
      (by norm_num : (1 : ℝ) + 0 ≠ 0) using 1
    all_goals norm_num
  have hden : Filter.Tendsto (fun n : ℕ => (n + 1 : ℝ)) Filter.atTop Filter.atTop :=
    by
      rw [Filter.tendsto_atTop]
      intro b
      obtain ⟨N, hN⟩ := exists_nat_ge b
      filter_upwards [Filter.eventually_ge_atTop N] with n hn
      have hn' : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
  have herr : Filter.Tendsto
      (fun n : ℕ => Real.log (1 + r ^ (n + 1)) / (n + 1 : ℝ))
      Filter.atTop (nhds 0) := by
    simpa using hlog.div_atTop hden
  have htotal : Filter.Tendsto
      (fun n : ℕ => Real.log (isingTransferEigenPlus beta h) +
        Real.log (1 + r ^ (n + 1)) / (n + 1 : ℝ))
      Filter.atTop (nhds (Real.log (isingTransferEigenPlus beta h))) := by
    simpa using (tendsto_const_nhds.add herr)
  refine htotal.congr' (Filter.Eventually.of_forall ?_)
  intro n
  haveI : NeZero (n + 1) := ⟨by omega⟩
  have hn : 0 < n + 1 := Nat.zero_lt_succ n
  have hp : 0 < isingTransferEigenPlus beta h :=
    isingTransfer_eigenPlus_pos beta h
  have hf : 0 < 1 + r ^ (n + 1) := isingRing_ratio_factor_pos beta h n
  change Real.log (isingTransferEigenPlus beta h) +
      Real.log (1 + r ^ (n + 1)) / (n + 1 : ℝ) =
    Real.log (isingRingZ (n + 1) beta h) / (n + 1 : ℝ)
  rw [isingRingZ_eigenvalues_real (n + 1) hn,
    isingRing_spectral_factor, Real.log_mul (pow_ne_zero _ hp.ne') hf.ne',
    Real.log_pow]
  dsimp only [r]
  field_simp
  push_cast
  ring

private lemma transfer_sum_closed_form (beta h : ℝ) :
    transferA beta h + transferD beta h =
      2 * Real.exp beta * Real.cosh h := by
  rw [transferA, transferD, Real.exp_add, Real.exp_sub, Real.cosh_eq,
    Real.exp_neg]
  field_simp [Real.exp_ne_zero]

private lemma transfer_diff_closed_form (beta h : ℝ) :
    transferA beta h - transferD beta h =
      2 * Real.exp beta * Real.sinh h := by
  rw [transferA, transferD, Real.exp_add, Real.exp_sub, Real.sinh_eq,
    Real.exp_neg]
  field_simp [Real.exp_ne_zero]

private lemma transferB_sq_closed_form (beta : ℝ) :
    transferB beta ^ 2 = Real.exp (-2 * beta) := by
  rw [transferB, pow_two, ← Real.exp_add]
  congr 1
  ring

private lemma exp_sq_closed_form (beta : ℝ) :
    Real.exp beta ^ 2 = Real.exp (2 * beta) := by
  rw [pow_two, ← Real.exp_add]
  congr 1
  ring


theorem isingTransferEigenPlus_closed_form (beta h : ℝ) :
    isingTransferEigenPlus beta h =
      Real.exp beta * Real.cosh h +
        Real.sqrt (Real.exp (2 * beta) * Real.sinh h ^ 2 +
          Real.exp (-2 * beta)) := by
  have hdisc : isingTransferDisc beta h =
      2 * Real.sqrt (Real.exp (2 * beta) * Real.sinh h ^ 2 +
        Real.exp (-2 * beta)) := by
    rw [isingTransferDisc, transfer_diff_closed_form,
      transferB_sq_closed_form, show
        (2 * Real.exp beta * Real.sinh h) ^ 2 + 4 * Real.exp (-2 * beta) =
          4 * (Real.exp (2 * beta) * Real.sinh h ^ 2 +
            Real.exp (-2 * beta)) by
        rw [← exp_sq_closed_form beta]
        ring]
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
  rw [isingTransferEigenPlus, transfer_sum_closed_form, hdisc]
  ring


theorem isingRing_pressure_closed_form (beta h : ℝ) :
    Filter.Tendsto
      (fun n : ℕ => Real.log (isingRingZ (n + 1) beta h) / (n + 1 : ℝ))
      Filter.atTop
      (nhds (Real.log (Real.exp beta * Real.cosh h +
        Real.sqrt (Real.exp (2 * beta) * Real.sinh h ^ 2 +
          Real.exp (-2 * beta))))) := by
  simpa only [isingTransferEigenPlus_closed_form] using
    isingRing_pressure_tendsto beta h



noncomputable def isingPressureClosedForm (x : ℝ × ℝ) : ℝ :=
  Real.log (Real.exp x.1 * Real.cosh x.2 +
    Real.sqrt (Real.exp (2 * x.1) * Real.sinh x.2 ^ 2 +
      Real.exp (-2 * x.1)))

private noncomputable def isingPressureRadicand (x : ℝ × ℝ) : ℝ :=
  Real.exp (2 * x.1) * Real.sinh x.2 ^ 2 + Real.exp (-2 * x.1)

private lemma isingPressureRadicand_pos (x : ℝ × ℝ) :
    0 < isingPressureRadicand x := by
  unfold isingPressureRadicand
  positivity

private lemma isingPressure_sqrt_eq_exp (x : ℝ × ℝ) :
    Real.sqrt (isingPressureRadicand x) =
      Real.exp (Real.log (isingPressureRadicand x) / 2) := by
  apply (Real.sqrt_eq_iff_eq_sq (isingPressureRadicand_pos x).le
    (Real.exp_pos _).le).2
  rw [pow_two, ← Real.exp_add]
  rw [show Real.log (isingPressureRadicand x) / 2 +
      Real.log (isingPressureRadicand x) / 2 =
      Real.log (isingPressureRadicand x) by ring,
    Real.exp_log (isingPressureRadicand_pos x)]

private theorem analyticAt_isingPressureRadicand (x : ℝ × ℝ) :
    AnalyticAt ℝ isingPressureRadicand x := by
  have hfst : AnalyticAt ℝ (fun y : ℝ × ℝ => y.1) x := analyticAt_fst
  have hsnd : AnalyticAt ℝ (fun y : ℝ × ℝ => y.2) x := analyticAt_snd
  have htwoFst : AnalyticAt ℝ (fun y : ℝ × ℝ => 2 * y.1) x :=
    analyticAt_const.mul hfst
  have hnegTwoFst : AnalyticAt ℝ (fun y : ℝ × ℝ => -2 * y.1) x :=
    analyticAt_const.mul hfst
  unfold isingPressureRadicand
  exact (htwoFst.rexp'.mul
    ((Real.analyticAt_sinh.comp hsnd).pow 2)).add hnegTwoFst.rexp'



theorem isingPressureClosedForm_analyticAt (x : ℝ × ℝ) :
    AnalyticAt ℝ isingPressureClosedForm x := by
  have hsqrtAlt : AnalyticAt ℝ
      (fun y : ℝ × ℝ =>
        Real.exp (Real.log (isingPressureRadicand y) / 2)) x := by
    exact ((analyticAt_log (isingPressureRadicand_pos x)).comp
      (analyticAt_isingPressureRadicand x)).div_const.rexp'
  have hsqrt : AnalyticAt ℝ
      (fun y : ℝ × ℝ => Real.sqrt (isingPressureRadicand y)) x := by
    exact hsqrtAlt.congr (Filter.Eventually.of_forall fun y =>
      (isingPressure_sqrt_eq_exp y).symm)
  have hlambda : AnalyticAt ℝ
      (fun y : ℝ × ℝ => Real.exp y.1 * Real.cosh y.2 +
        Real.sqrt (isingPressureRadicand y)) x := by
    have hfst : AnalyticAt ℝ (fun y : ℝ × ℝ => y.1) x := analyticAt_fst
    have hsnd : AnalyticAt ℝ (fun y : ℝ × ℝ => y.2) x := analyticAt_snd
    apply AnalyticAt.add
    · exact hfst.rexp'.mul (Real.analyticAt_cosh.comp hsnd)
    · exact hsqrt
  have hlambdaPos : 0 < Real.exp x.1 * Real.cosh x.2 +
      Real.sqrt (isingPressureRadicand x) := by
    positivity
  unfold isingPressureClosedForm
  change AnalyticAt ℝ
    (fun y : ℝ × ℝ => Real.log (Real.exp y.1 * Real.cosh y.2 +
      Real.sqrt (isingPressureRadicand y))) x
  exact AnalyticAt.comp'
    (f := fun y : ℝ × ℝ => Real.exp y.1 * Real.cosh y.2 +
      Real.sqrt (isingPressureRadicand y))
    (analyticAt_log hlambdaPos) hlambda


noncomputable def isingTransferCorrelationRatio (beta h : ℝ) : ℝ :=
  isingTransferEigenMinus beta h / isingTransferEigenPlus beta h

private lemma transferAD_closed_form (beta h : ℝ) :
    transferA beta h * transferD beta h = Real.exp (2 * beta) := by
  rw [transferA, transferD, ← Real.exp_add]
  congr 1
  ring

lemma isingTransfer_eigenMinus_nonneg {beta : ℝ} (hbeta : 0 ≤ beta) (h : ℝ) :
    0 ≤ isingTransferEigenMinus beta h := by
  have hexp : Real.exp (-2 * beta) ≤ Real.exp (2 * beta) := by
    rw [Real.exp_le_exp]
    linarith
  have hprod : 0 ≤ isingTransferEigenPlus beta h *
      isingTransferEigenMinus beta h := by
    rw [isingTransfer_eigen_prod, transferAD_closed_form,
      transferB_sq_closed_form]
    linarith
  nlinarith [isingTransfer_eigenPlus_pos beta h]



theorem isingTransferCorrelationRatio_mem_Ico {beta : ℝ} (hbeta : 0 ≤ beta)
    (h : ℝ) : isingTransferCorrelationRatio beta h ∈ Set.Ico 0 1 := by
  have hnonneg : 0 ≤ isingTransferCorrelationRatio beta h :=
    div_nonneg (isingTransfer_eigenMinus_nonneg hbeta h)
      (isingTransfer_eigenPlus_pos beta h).le
  refine ⟨hnonneg, ?_⟩
  have habs := isingTransfer_eigenRatio_abs_lt_one beta h
  change |isingTransferCorrelationRatio beta h| < 1 at habs
  rw [abs_of_nonneg hnonneg] at habs
  exact habs


theorem isingTransferCorrelationRatio_pow_tendsto_zero {beta : ℝ}
    (hbeta : 0 ≤ beta) (h : ℝ) :
    Filter.Tendsto (fun n : ℕ => isingTransferCorrelationRatio beta h ^ n)
      Filter.atTop (nhds 0) := by
  have hr := isingTransferCorrelationRatio_mem_Ico hbeta h
  apply tendsto_pow_atTop_nhds_zero_of_abs_lt_one
  rw [abs_of_nonneg hr.1]
  exact hr.2

end StatMech.FrontierC
