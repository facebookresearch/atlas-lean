/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.MeasureTheory.Function.SpecialFunctions.Sinc

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import MathlibExt.Probability.InfinitelyDivisible

import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.MeasureTheory.Measure.IntegralCharFun
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.Topology.Connected.TotallyDisconnected

/-!
# The Lévy–Khintchin representation

This file proves the one-dimensional Lévy–Khintchin characterization of infinitely divisible
probability measures, with the hard truncation convention at radius one.
-/

open MeasureTheory
open scoped ENNReal NNReal MeasureTheory Topology

namespace MetaMathlibExt

@[expose] public section

private noncomputable def lkJump (t x : ℝ) : ℂ :=
  Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)) - 1 -
    Set.indicator {y : ℝ | |y| ≤ 1} (fun y ↦ Complex.I * (t : ℂ) * (y : ℂ)) x

private lemma lkJump_of_abs_le (t : ℝ) {x : ℝ} (hx : |x| ≤ 1) :
    lkJump t x = Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)) - 1 -
      Complex.I * (t : ℂ) * (x : ℂ) := by
  simp [lkJump, hx]

private lemma lkJump_of_one_lt_abs (t : ℝ) {x : ℝ} (hx : 1 < |x|) :
    lkJump t x = Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)) - 1 := by
  simp [lkJump, not_le_of_gt hx]

@[simp]
private lemma lkJump_zero (t : ℝ) : lkJump t 0 = 0 := by
  simp [lkJump]

@[simp]
private lemma lkJump_zero_time (x : ℝ) : lkJump 0 x = 0 := by
  simp [lkJump]

private lemma lk_norm_jump_le (t x : ℝ) :
    ‖lkJump t x‖ ≤ max 2 (t ^ 2 * Real.exp |t|) * min 1 (x ^ 2) := by
  by_cases hx : |x| ≤ 1
  · rw [lkJump_of_abs_le t hx, min_eq_right ((sq_le_one_iff_abs_le_one x).mpr hx)]
    let z : ℂ := Complex.I * (t : ℂ) * (x : ℂ)
    have hrem : ‖Complex.exp z - 1 - z‖ ≤ ‖z‖ ^ 2 * Real.exp ‖z‖ := by
      have h := Complex.norm_exp_sub_sum_le_norm_mul_exp z 2
      norm_num [Finset.sum_range_succ] at h
      simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using h
    rw [show Complex.I * (t : ℂ) * (x : ℂ) = z from rfl]
    calc
      ‖Complex.exp z - 1 - z‖ ≤ ‖z‖ ^ 2 * Real.exp ‖z‖ := hrem
      _ ≤ (|t| * |x|) ^ 2 * Real.exp |t| := by
        simp only [z, Complex.norm_mul, Complex.norm_I, Complex.norm_real, one_mul,
          Real.norm_eq_abs]
        gcongr
        exact mul_le_of_le_one_right (abs_nonneg t) hx
      _ = t ^ 2 * Real.exp |t| * x ^ 2 := by
        rw [mul_pow, sq_abs, sq_abs]
        ring
      _ ≤ max 2 (t ^ 2 * Real.exp |t|) * x ^ 2 :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg x)
  · have hx' : 1 < |x| := lt_of_not_ge hx
    rw [lkJump_of_one_lt_abs t hx', min_eq_left ((one_le_sq_iff_one_le_abs x).mpr hx'.le),
      mul_one]
    calc
      ‖Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)) - 1‖
          ≤ ‖Complex.exp (Complex.I * (t : ℂ) * (x : ℂ))‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by
        rw [show Complex.I * (t : ℂ) * (x : ℂ) = ((t * x : ℝ) : ℂ) * Complex.I by
          push_cast
          ring]
        rw [Complex.norm_exp_ofReal_mul_I]
        norm_num [Complex.norm_def]
      _ ≤ max 2 (t ^ 2 * Real.exp |t|) := le_max_left _ _

private lemma lk_norm_jump_le_of_abs_le {R t : ℝ} (hR : 0 ≤ R) (ht : |t| ≤ R) (x : ℝ) :
    ‖lkJump t x‖ ≤ max 2 (R ^ 2 * Real.exp R) * min 1 (x ^ 2) := by
  have h_sq : t ^ 2 ≤ R ^ 2 := by
    rw [← sq_abs t]
    exact (sq_le_sq₀ (abs_nonneg t) hR).2 ht
  have h_coeff : t ^ 2 * Real.exp |t| ≤ R ^ 2 * Real.exp R := by
    gcongr
  exact (lk_norm_jump_le t x).trans <|
    mul_le_mul_of_nonneg_right (max_le_max_left 2 h_coeff) (by positivity)

private lemma lk_jump_stronglyMeasurable (t : ℝ) : StronglyMeasurable (lkJump t) := by
  unfold lkJump
  have h_exp : StronglyMeasurable
      (fun x : ℝ ↦ Complex.exp (Complex.I * (t : ℂ) * (x : ℂ))) :=
    (by fun_prop : Continuous
      (fun x : ℝ ↦ Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)))).stronglyMeasurable
  have h_linear : StronglyMeasurable (fun x : ℝ ↦ Complex.I * (t : ℂ) * (x : ℂ)) :=
    (by fun_prop : Continuous (fun x : ℝ ↦ Complex.I * (t : ℂ) * (x : ℂ))).stronglyMeasurable
  exact (h_exp.sub stronglyMeasurable_const).sub <|
    h_linear.indicator <| (isClosed_le (by fun_prop) (by fun_prop)).measurableSet

private lemma lk_moment_integrable {ν : Measure ℝ}
    (hν : ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂ν < ∞) :
    Integrable (fun x : ℝ ↦ min 1 (x ^ 2)) ν := by
  have h_nonneg : 0 ≤ᵐ[ν] fun x : ℝ ↦ min 1 (x ^ 2) :=
    ae_of_all ν fun x ↦ by positivity
  have h_cont : Continuous (fun x : ℝ ↦ min 1 (x ^ 2)) := by fun_prop
  refine ⟨h_cont.stronglyMeasurable.aestronglyMeasurable, ?_⟩
  exact (hasFiniteIntegral_iff_ofReal h_nonneg).2 hν

private lemma lk_jump_integrable {ν : Measure ℝ}
    (hν : ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂ν < ∞) (t : ℝ) :
    Integrable (lkJump t) ν := by
  exact ((lk_moment_integrable hν).const_mul (max 2 (t ^ 2 * Real.exp |t|))).mono'
    (lk_jump_stronglyMeasurable t).aestronglyMeasurable
    (ae_of_all ν fun x ↦ lk_norm_jump_le t x)

private lemma lk_jump_integral_continuous {ν : Measure ℝ}
    (hν : ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂ν < ∞) :
    Continuous (fun t : ℝ ↦ ∫ x, lkJump t x ∂ν) := by
  rw [continuous_iff_continuousAt]
  intro t₀
  let R : ℝ := |t₀| + 1
  let C : ℝ := max 2 (R ^ 2 * Real.exp R)
  apply continuousAt_of_dominated (bound := fun x : ℝ ↦ C * min 1 (x ^ 2))
  · exact Filter.Eventually.of_forall fun t ↦
      (lk_jump_stronglyMeasurable t).aestronglyMeasurable
  · filter_upwards [Metric.ball_mem_nhds t₀ zero_lt_one] with t ht
    have ht_dist : |t - t₀| < 1 := by simpa [Real.dist_eq] using ht
    have ht_abs : |t| ≤ R := by
      rw [show t = (t - t₀) + t₀ by ring]
      calc
        |t - t₀ + t₀| ≤ |t - t₀| + |t₀| := abs_add_le _ _
        _ ≤ R := by simp only [R]; linarith
    exact ae_of_all ν fun x ↦ lk_norm_jump_le_of_abs_le (by dsimp [R]; positivity) ht_abs x
  · exact (lk_moment_integrable hν).const_mul C
  · exact ae_of_all ν fun x ↦ by
      unfold lkJump
      by_cases hx : |x| ≤ 1
      · simp only [Set.indicator_of_mem (s := {y : ℝ | |y| ≤ 1}) hx]
        fun_prop
      · simp only [Set.indicator_of_notMem (s := {y : ℝ | |y| ≤ 1}) hx]
        fun_prop

private noncomputable def lkExponent (γ σ : ℝ) (ν : Measure ℝ) (t : ℝ) : ℂ :=
  Complex.I * (γ : ℂ) * (t : ℂ) - (((σ ^ 2 * t ^ 2 : ℝ) : ℂ) / 2) +
    ∫ x, lkJump t x ∂ν

@[simp]
private lemma lkExponent_zero (γ σ : ℝ) (ν : Measure ℝ) : lkExponent γ σ ν 0 = 0 := by
  simp [lkExponent]

private lemma lk_exponent_continuous {ν : Measure ℝ}
    (hν : ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂ν < ∞) (γ σ : ℝ) :
    Continuous (lkExponent γ σ ν) := by
  have h_int := lk_jump_integral_continuous hν
  unfold lkExponent
  fun_prop

private noncomputable def lkCutoff (k : ℕ) : ℝ := ((k + 1 : ℕ) : ℝ)⁻¹

private def lkTruncationSet (k : ℕ) : Set ℝ := {x | lkCutoff k < |x|}

private lemma lkTruncationSet_measurable (k : ℕ) : MeasurableSet (lkTruncationSet k) := by
  exact (isOpen_lt (by fun_prop) (by fun_prop)).measurableSet

private noncomputable def lkTruncate (ν : Measure ℝ) (k : ℕ) : Measure ℝ :=
  ν.restrict (lkTruncationSet k)

private lemma lkCutoff_pos (k : ℕ) : 0 < lkCutoff k := by
  simp only [lkCutoff]
  positivity

private lemma lkCutoff_le_one (k : ℕ) : lkCutoff k ≤ 1 := by
  simp only [lkCutoff]
  apply (inv_le_one₀ (by positivity)).2
  norm_num

private lemma lkCutoff_tendsto_zero : Filter.Tendsto lkCutoff Filter.atTop (𝓝 0) := by
  have h :=
    (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (Filter.tendsto_add_atTop_nat 1)
  exact h.congr' <| Filter.Eventually.of_forall fun k ↦ by rfl

private lemma lk_indicator_truncation_tendsto (t x : ℝ) :
    Filter.Tendsto
      (fun k : ℕ ↦ Set.indicator (lkTruncationSet k) (lkJump t) x)
      Filter.atTop (𝓝 (lkJump t x)) := by
  by_cases hx : x = 0
  · subst x
    refine tendsto_const_nhds.congr' (Filter.Eventually.of_forall fun k ↦ ?_)
    by_cases h0 : 0 ∈ lkTruncationSet k
    · simp [Set.indicator_of_mem h0]
    · simp [Set.indicator_of_notMem h0]
  · have hxpos : 0 < |x| := abs_pos.mpr hx
    have hev : ∀ᶠ k : ℕ in Filter.atTop, lkCutoff k < |x| :=
      lkCutoff_tendsto_zero.eventually (gt_mem_nhds hxpos)
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hev] with k hk
    exact (Set.indicator_of_mem (f := lkJump t)
      (show x ∈ lkTruncationSet k from hk)).symm

private lemma lk_cutoff_sq_le_moment {k : ℕ} {x : ℝ} (hx : x ∈ lkTruncationSet k) :
    lkCutoff k ^ 2 ≤ min 1 (x ^ 2) := by
  apply le_min
  · simpa using (sq_le_sq₀ (lkCutoff_pos k).le zero_le_one).2 (lkCutoff_le_one k)
  · rw [← sq_abs x]
    exact (sq_le_sq₀ (lkCutoff_pos k).le (abs_nonneg x)).2 hx.le

private lemma lk_restrict_away_zero_finite {ν : Measure ℝ}
    (hν : ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂ν < ∞) (k : ℕ) :
    IsFiniteMeasure (lkTruncate ν k) := by
  apply IsFiniteMeasure.mk
  let ε : ℝ≥0∞ := ENNReal.ofReal (lkCutoff k ^ 2)
  have hε : ε ≠ 0 := by
    dsimp only [ε]
    exact ne_of_gt (ENNReal.ofReal_pos.2 (sq_pos_of_pos (lkCutoff_pos k)))
  have h_meas : AEMeasurable (fun x : ℝ ↦ ENNReal.ofReal (min 1 (x ^ 2))) ν := by
    have h_cont : Continuous (fun x : ℝ ↦ min 1 (x ^ 2)) := by fun_prop
    exact h_cont.measurable.aemeasurable.ennreal_ofReal
  calc
    lkTruncate ν k Set.univ = ν (lkTruncationSet k) := by
      rw [lkTruncate, Measure.restrict_apply MeasurableSet.univ]
      simp
    _ ≤ ν {x | ε ≤ ENNReal.ofReal (min 1 (x ^ 2))} := by
      apply measure_mono
      intro x hx
      exact ENNReal.ofReal_le_ofReal (lk_cutoff_sq_le_moment hx)
    _ ≤ (∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂ν) / ε :=
      meas_ge_le_lintegral_div h_meas hε ENNReal.ofReal_ne_top
    _ < ∞ := ENNReal.div_lt_top (ne_of_lt hν) hε

private lemma lkConvPow_finite (ρ : Measure ℝ) [IsFiniteMeasure ρ] (n : ℕ) :
    IsFiniteMeasure (Measure.convPow ρ n) := by
  induction n with
  | zero =>
      rw [Measure.convPow]
      infer_instance
  | succ n ih =>
      rw [Measure.convPow]
      infer_instance

private lemma lk_charFun_convPow (ρ : Measure ℝ) [IsFiniteMeasure ρ] (n : ℕ) (t : ℝ) :
    charFun (Measure.convPow ρ n) t = charFun ρ t ^ n := by
  induction n with
  | zero => simp [Measure.convPow, charFun_dirac]
  | succ n ih =>
      rw [Measure.convPow]
      let _ := lkConvPow_finite ρ n
      rw [charFun_conv, ih, pow_succ]

private lemma lk_conv_apply_univ (μ ν : Measure ℝ) [SFinite μ] [SFinite ν] :
    (μ ∗ ν) Set.univ = μ Set.univ * ν Set.univ := by
  rw [Measure.conv, Measure.map_apply_of_aemeasurable (by fun_prop) MeasurableSet.univ]
  simp only [Set.preimage_univ]
  rw [Measure.prod_apply MeasurableSet.univ]
  simp [mul_comm]

private lemma lkConvPow_apply_univ (ρ : Measure ℝ) [IsFiniteMeasure ρ] (n : ℕ) :
    Measure.convPow ρ n Set.univ = ρ Set.univ ^ n := by
  induction n with
  | zero => simp [Measure.convPow]
  | succ n ih =>
      rw [Measure.convPow]
      let _ := lkConvPow_finite ρ n
      rw [lk_conv_apply_univ, ih, pow_succ]

private noncomputable def lkPoissonCoeff (ρ : Measure ℝ) (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-ρ.real Set.univ) / (n.factorial : ℝ))

private noncomputable def lkCompoundPoisson (ρ : Measure ℝ) : Measure ℝ :=
  Measure.sum fun n : ℕ ↦ lkPoissonCoeff ρ n • Measure.convPow ρ n

private lemma lk_hasSum_poisson (lam : ℝ) :
    HasSum (fun n : ℕ ↦ Real.exp (-lam) * lam ^ n / (n.factorial : ℝ)) 1 := by
  have h := HasSum.mul_left (Real.exp (-lam)) (NormedSpace.expSeries_div_hasSum_exp lam)
  have h' : HasSum (fun n : ℕ ↦ Real.exp (-lam) * lam ^ n / (n.factorial : ℝ))
      (Real.exp (-lam) * NormedSpace.exp lam) := by
    refine h.congr_fun ?_
    intro n
    ring
  rw [← Real.exp_eq_exp_ℝ, ← Real.exp_add] at h'
  simpa using h'

private lemma lk_compound_term_univ (ρ : Measure ℝ) [IsFiniteMeasure ρ] (n : ℕ) :
    (lkPoissonCoeff ρ n • Measure.convPow ρ n) Set.univ =
      ENNReal.ofReal
        (Real.exp (-ρ.real Set.univ) * (ρ.real Set.univ) ^ n / (n.factorial : ℝ)) := by
  rw [Measure.smul_apply, lkConvPow_apply_univ]
  simp only [smul_eq_mul, lkPoissonCoeff]
  let lam : ℝ := ρ.real Set.univ
  change ENNReal.ofReal (Real.exp (-lam) / (n.factorial : ℝ)) * (ρ Set.univ) ^ n =
    ENNReal.ofReal (Real.exp (-lam) * lam ^ n / (n.factorial : ℝ))
  have hmass : ρ Set.univ = ENNReal.ofReal lam :=
    (ENNReal.ofReal_toReal (measure_ne_top ρ Set.univ)).symm
  have hlam : 0 ≤ lam := ENNReal.toReal_nonneg
  rw [hmass, ← ENNReal.ofReal_pow hlam]
  rw [← ENNReal.ofReal_mul (by positivity :
    0 ≤ Real.exp (-lam) / (n.factorial : ℝ))]
  congr 1
  ring

private lemma lk_compoundPoisson_probability (ρ : Measure ℝ) [IsFiniteMeasure ρ] :
    IsProbabilityMeasure (lkCompoundPoisson ρ) := by
  rw [isProbabilityMeasure_iff, lkCompoundPoisson, Measure.sum_apply _ MeasurableSet.univ]
  simp_rw [lk_compound_term_univ]
  let lam : ℝ := ρ.real Set.univ
  change (∑' n : ℕ,
    ENNReal.ofReal (Real.exp (-lam) * lam ^ n / (n.factorial : ℝ))) = 1
  have hlam : 0 ≤ lam := ENNReal.toReal_nonneg
  have hsum := lk_hasSum_poisson lam
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n ↦ by positivity) hsum.summable, hsum.tsum_eq]
  norm_num

private lemma lkPoissonCoeff_toReal (ρ : Measure ℝ) (n : ℕ) :
    (lkPoissonCoeff ρ n).toReal =
      Real.exp (-ρ.real Set.univ) / (n.factorial : ℝ) := by
  rw [lkPoissonCoeff, ENNReal.toReal_ofReal]
  positivity

private lemma lk_charFun_compoundPoisson_aux (ρ : Measure ℝ) [IsFiniteMeasure ρ] (t : ℝ) :
    charFun (lkCompoundPoisson ρ) t =
      Complex.exp (charFun ρ t - (ρ.real Set.univ : ℂ)) := by
  let _ := lk_compoundPoisson_probability ρ
  have h_integrable : Integrable (BoundedContinuousFunction.innerProbChar t)
      (lkCompoundPoisson ρ) :=
    (BoundedContinuousFunction.innerProbChar t).integrable _
  rw [charFun_eq_integral_innerProbChar, lkCompoundPoisson]
  rw [integral_sum_measure h_integrable]
  simp_rw [integral_smul_measure, ← charFun_eq_integral_innerProbChar,
    lk_charFun_convPow, lkPoissonCoeff_toReal, Complex.real_smul]
  let lam : ℝ := ρ.real Set.univ
  let z : ℂ := charFun ρ t
  change (∑' n : ℕ, ((Real.exp (-lam) / (n.factorial : ℝ) : ℝ) : ℂ) * z ^ n) =
    Complex.exp (z - (lam : ℂ))
  have h := HasSum.mul_left (Real.exp (-lam) : ℂ)
    (NormedSpace.expSeries_div_hasSum_exp z)
  have h' : HasSum
      (fun n : ℕ ↦ ((Real.exp (-lam) / (n.factorial : ℝ) : ℝ) : ℂ) * z ^ n)
      (Real.exp (-lam) * NormedSpace.exp z) := by
    refine h.congr_fun ?_
    intro n
    push_cast
    ring
  rw [Complex.ofReal_exp, ← Complex.exp_eq_exp_ℂ, ← Complex.exp_add] at h'
  rw [h'.tsum_eq]
  congr 1
  push_cast
  ring

private lemma lk_integrable_exp_mul_I (ρ : Measure ℝ) [IsFiniteMeasure ρ] (t : ℝ) :
    Integrable (fun x : ℝ ↦ Complex.exp (Complex.I * (t : ℂ) * (x : ℂ))) ρ := by
  have h_cont : Continuous
      (fun x : ℝ ↦ Complex.exp (Complex.I * (t : ℂ) * (x : ℂ))) := by fun_prop
  refine Integrable.of_bound h_cont.stronglyMeasurable.aestronglyMeasurable 1 ?_
  exact ae_of_all ρ fun x ↦ by
    rw [show Complex.I * (t : ℂ) * (x : ℂ) = ((t * x : ℝ) : ℂ) * Complex.I by
      push_cast
      ring]
    rw [Complex.norm_exp_ofReal_mul_I]

private lemma lk_charFun_compoundPoisson (ρ : Measure ℝ) [IsFiniteMeasure ρ] (t : ℝ) :
    charFun (lkCompoundPoisson ρ) t =
      Complex.exp (∫ x, Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)) - 1 ∂ρ) := by
  rw [lk_charFun_compoundPoisson_aux]
  congr 1
  have h_fun :
      (fun x : ℝ ↦ Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I)) =
        fun x : ℝ ↦ Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)) := by
    funext x
    congr 1
    ring
  rw [charFun_apply_real, h_fun]
  rw [integral_sub (lk_integrable_exp_mul_I ρ t) (integrable_const 1)]
  rw [integral_const]
  simp [Complex.real_smul]

private noncomputable def lkCompensation (ν : Measure ℝ) (k : ℕ) : ℝ :=
  ∫ x, Set.indicator {y : ℝ | |y| ≤ 1} id x ∂lkTruncate ν k

private lemma lk_compensation_integrable {ν : Measure ℝ}
    (hν : ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂ν < ∞) (k : ℕ) :
    Integrable (Set.indicator {y : ℝ | |y| ≤ 1} id) (lkTruncate ν k) := by
  let _ := lk_restrict_away_zero_finite hν k
  have h_meas : StronglyMeasurable (Set.indicator {y : ℝ | |y| ≤ 1} id) :=
    stronglyMeasurable_id.indicator <| (isClosed_le (by fun_prop) (by fun_prop)).measurableSet
  apply Integrable.of_bound h_meas.aestronglyMeasurable 1
  exact ae_of_all _ fun x ↦ by
    by_cases hx : |x| ≤ 1
    · rw [Set.indicator_of_mem (show x ∈ {y : ℝ | |y| ≤ 1} from hx)]
      simpa [Real.norm_eq_abs] using hx
    · rw [Set.indicator_of_notMem (show x ∉ {y : ℝ | |y| ≤ 1} from hx)]
      simp

private lemma lk_integral_compensation (ν : Measure ℝ) (k : ℕ) (t : ℝ) :
    (∫ x, Set.indicator {y : ℝ | |y| ≤ 1}
        (fun y ↦ Complex.I * (t : ℂ) * (y : ℂ)) x ∂lkTruncate ν k) =
      Complex.I * (t : ℂ) * (lkCompensation ν k : ℂ) := by
  have h_fun :
      (fun x : ℝ ↦ Set.indicator {y : ℝ | |y| ≤ 1}
        (fun y ↦ Complex.I * (t : ℂ) * (y : ℂ)) x) =
        fun x ↦ Complex.I * (t : ℂ) *
          ((Set.indicator {y : ℝ | |y| ≤ 1} (id : ℝ → ℝ) x : ℝ) : ℂ) := by
    funext x
    by_cases hx : |x| ≤ 1 <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx]
  rw [h_fun, integral_const_mul, integral_complex_ofReal]
  rfl

private lemma lk_linear_integrable_truncate {ν : Measure ℝ}
    (hν : ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂ν < ∞) (k : ℕ) (t : ℝ) :
    Integrable (Set.indicator {y : ℝ | |y| ≤ 1}
      (fun y ↦ Complex.I * (t : ℂ) * (y : ℂ))) (lkTruncate ν k) := by
  have h := (lk_compensation_integrable hν k).ofReal.const_mul
    (Complex.I * (t : ℂ))
  refine h.congr (ae_of_all _ fun x ↦ ?_)
  by_cases hx : |x| ≤ 1 <;> simp [hx]

private lemma lk_integral_jump_truncate {ν : Measure ℝ}
    (hν : ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂ν < ∞) (k : ℕ) (t : ℝ) :
    (∫ x, Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)) - 1 ∂lkTruncate ν k) -
        Complex.I * (t : ℂ) * (lkCompensation ν k : ℂ) =
      ∫ x, lkJump t x ∂lkTruncate ν k := by
  let _ := lk_restrict_away_zero_finite hν k
  have h_exp := lk_integrable_exp_mul_I (lkTruncate ν k) t
  have h_sub : Integrable
      (fun x : ℝ ↦ Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)) - 1)
      (lkTruncate ν k) := h_exp.sub (integrable_const 1)
  rw [← lk_integral_compensation ν k t]
  rw [← integral_sub h_sub (lk_linear_integrable_truncate hν k t)]
  rfl

private def lkVariance (σ : ℝ) : NNReal := ⟨σ ^ 2, sq_nonneg σ⟩

@[simp]
private lemma lkVariance_coe (σ : ℝ) : (lkVariance σ : ℝ) = σ ^ 2 := rfl

private noncomputable def lkTruncatedLaw (γ σ : ℝ) (ν : Measure ℝ) (k : ℕ) : Measure ℝ :=
  (lkCompoundPoisson (lkTruncate ν k) ∗ Measure.dirac (γ - lkCompensation ν k)) ∗
    ProbabilityTheory.gaussianReal 0 (lkVariance σ)

private lemma lkTruncatedLaw_probability {ν : Measure ℝ}
    (hν : ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂ν < ∞) (γ σ : ℝ) (k : ℕ) :
    IsProbabilityMeasure (lkTruncatedLaw γ σ ν k) := by
  let h_trunc := lk_restrict_away_zero_finite hν k
  let h_cp := @lk_compoundPoisson_probability (lkTruncate ν k) h_trunc
  unfold lkTruncatedLaw
  have h_left : IsProbabilityMeasure
      (lkCompoundPoisson (lkTruncate ν k) ∗ Measure.dirac (γ - lkCompensation ν k)) := by
    infer_instance
  exact @Measure.probabilitymeasure_of_probabilitymeasures_conv ℝ _ _ _ _ h_left
    (ProbabilityTheory.instIsProbabilityMeasureGaussianReal 0 (lkVariance σ))

private lemma lk_charFun_truncatedLaw {ν : Measure ℝ}
    (hν : ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂ν < ∞)
    (γ σ t : ℝ) (k : ℕ) :
    charFun (lkTruncatedLaw γ σ ν k) t =
      Complex.exp (lkExponent γ σ (lkTruncate ν k) t) := by
  let h_trunc := lk_restrict_away_zero_finite hν k
  let h_cp := @lk_compoundPoisson_probability (lkTruncate ν k) h_trunc
  let h_left : IsProbabilityMeasure
      (lkCompoundPoisson (lkTruncate ν k) ∗ Measure.dirac (γ - lkCompensation ν k)) := by
    infer_instance
  let h_gauss := ProbabilityTheory.instIsProbabilityMeasureGaussianReal 0 (lkVariance σ)
  unfold lkTruncatedLaw
  rw [charFun_conv, charFun_conv, lk_charFun_compoundPoisson, charFun_dirac]
  rw [ProbabilityTheory.charFun_gaussianReal
    (μ := 0) (v := lkVariance σ)]
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  unfold lkExponent
  rw [← lk_integral_jump_truncate hν k t]
  push_cast
  simp only [Real.inner_apply, lkVariance_coe]
  push_cast
  ring

private lemma lk_integral_truncate_tendsto {ν : Measure ℝ}
    (hν : ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂ν < ∞) (t : ℝ) :
    Filter.Tendsto (fun k : ℕ ↦ ∫ x, lkJump t x ∂lkTruncate ν k) Filter.atTop
      (𝓝 (∫ x, lkJump t x ∂ν)) := by
  let C : ℝ := max 2 (t ^ 2 * Real.exp |t|)
  have h_dc : Filter.Tendsto
      (fun k : ℕ ↦ ∫ x, Set.indicator (lkTruncationSet k) (lkJump t) x ∂ν)
      Filter.atTop (𝓝 (∫ x, lkJump t x ∂ν)) := by
    apply tendsto_integral_of_dominated_convergence
      (fun x : ℝ ↦ C * min 1 (x ^ 2))
    · intro k
      exact ((lk_jump_stronglyMeasurable t).indicator
        (lkTruncationSet_measurable k)).aestronglyMeasurable
    · exact (lk_moment_integrable hν).const_mul C
    · intro k
      exact ae_of_all ν fun x ↦ by
        by_cases hx : x ∈ lkTruncationSet k
        · rw [Set.indicator_of_mem hx]
          exact lk_norm_jump_le t x
        · rw [Set.indicator_of_notMem hx, norm_zero]
          positivity
    · exact ae_of_all ν fun x ↦ lk_indicator_truncation_tendsto t x
  refine h_dc.congr' (Filter.Eventually.of_forall fun k ↦ ?_)
  simpa only [lkTruncate] using
    (integral_indicator (μ := ν) (f := lkJump t) (lkTruncationSet_measurable k))

private lemma lk_exponent_truncate_tendsto {ν : Measure ℝ}
    (hν : ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂ν < ∞) (γ σ t : ℝ) :
    Filter.Tendsto (fun k : ℕ ↦ lkExponent γ σ (lkTruncate ν k) t) Filter.atTop
      (𝓝 (lkExponent γ σ ν t)) := by
  have h := (tendsto_const_nhds (x :=
    Complex.I * (γ : ℂ) * (t : ℂ) - (((σ ^ 2 * t ^ 2 : ℝ) : ℂ) / 2))).add
      (lk_integral_truncate_tendsto hν t)
  simpa only [lkExponent] using h

private lemma lk_charFun_truncatedLaw_tendsto {ν : Measure ℝ}
    (hν : ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂ν < ∞) (γ σ t : ℝ) :
    Filter.Tendsto (fun k : ℕ ↦ charFun (lkTruncatedLaw γ σ ν k) t) Filter.atTop
      (𝓝 (Complex.exp (lkExponent γ σ ν t))) := by
  have h_exp : Filter.Tendsto
      (fun k : ℕ ↦ Complex.exp (lkExponent γ σ (lkTruncate ν k) t)) Filter.atTop
      (𝓝 (Complex.exp (lkExponent γ σ ν t))) := by
    have h := ((by fun_prop : Continuous Complex.exp).tendsto (lkExponent γ σ ν t)).comp
      (lk_exponent_truncate_tendsto hν γ σ t)
    exact h.congr' <| Filter.Eventually.of_forall fun k ↦ by rfl
  refine h_exp.congr' (Filter.Eventually.of_forall fun k ↦ ?_)
  exact (lk_charFun_truncatedLaw hν γ σ t k).symm

private noncomputable def lkApproxPM (γ σ : ℝ) (ν : Measure ℝ)
    (hν : ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂ν < ∞) (k : ℕ) :
    ProbabilityMeasure ℝ :=
  ⟨lkTruncatedLaw γ σ ν k, lkTruncatedLaw_probability hν γ σ k⟩

@[simp]
private lemma lkApproxPM_toMeasure (γ σ : ℝ) (ν : Measure ℝ)
    (hν : ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂ν < ∞) (k : ℕ) :
    (lkApproxPM γ σ ν hν k : Measure ℝ) = lkTruncatedLaw γ σ ν k := rfl

private lemma lk_exists_probabilityMeasure_charFun {ν : Measure ℝ}
    (hν : ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂ν < ∞) (γ σ : ℝ) :
    ∃ μ : ProbabilityMeasure ℝ,
      ∀ t : ℝ, charFun (μ : Measure ℝ) t = Complex.exp (lkExponent γ σ ν t) := by
  let μk : ℕ → ProbabilityMeasure ℝ := lkApproxPM γ σ ν hν
  let f : ℝ → ℂ := fun t ↦ Complex.exp (lkExponent γ σ ν t)
  have hf : ContinuousAt f 0 := by
    exact ((by fun_prop : Continuous Complex.exp).comp
      (lk_exponent_continuous hν γ σ)).continuousAt
  have h_tight : IsTightMeasureSet (Set.range fun k ↦ (μk k : Measure ℝ)) := by
    apply isTightMeasureSet_of_tendsto_charFun hf
    intro t
    exact lk_charFun_truncatedLaw_tendsto hν γ σ t
  let _ := TopologicalSpace.metrizableSpaceMetric (ProbabilityMeasure ℝ)
  have h_compact : IsCompact (closure (Set.range μk)) := by
    apply isCompact_closure_of_isTightMeasureSet
    rw [show {x : Measure ℝ | ∃ μ ∈ Set.range μk, (μ : Measure ℝ) = x} =
        Set.range (fun k ↦ (μk k : Measure ℝ)) by
      ext x
      constructor
      · rintro ⟨μ, ⟨k, rfl⟩, rfl⟩
        exact ⟨k, rfl⟩
      · rintro ⟨k, rfl⟩
        exact ⟨μk k, ⟨k, rfl⟩, rfl⟩]
    exact h_tight
  obtain ⟨μ, -, r, hr, hμ⟩ := h_compact.isSeqCompact
    (fun k ↦ subset_closure (Set.mem_range_self k))
  refine ⟨μ, fun t ↦ ?_⟩
  have h_char := ProbabilityMeasure.tendsto_iff_tendsto_charFun.mp hμ t
  have h_sub := (lk_charFun_truncatedLaw_tendsto hν γ σ t).comp hr.tendsto_atTop
  exact tendsto_nhds_unique h_char h_sub

private noncomputable def lkRootScale (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal ((n : ℝ)⁻¹)

private noncomputable def lkRootMeasure (n : ℕ) (ν : Measure ℝ) : Measure ℝ :=
  lkRootScale n • ν

private lemma lk_root_moment {ν : Measure ℝ}
    (hν : ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂ν < ∞) (n : ℕ) :
    ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂lkRootMeasure n ν < ∞ := by
  rw [lkRootMeasure, lintegral_smul_measure]
  change lkRootScale n * (∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂ν) < ∞
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hν

private noncomputable def lkRootSigma (σ : ℝ) (n : ℕ) : ℝ :=
  Real.sqrt (σ ^ 2 / (n : ℝ))

private lemma lkRootSigma_sq (σ : ℝ) (n : ℕ) :
    lkRootSigma σ n ^ 2 = σ ^ 2 / (n : ℝ) := by
  exact Real.sq_sqrt (div_nonneg (sq_nonneg σ) (Nat.cast_nonneg n))

private lemma lkRootScale_toReal (n : ℕ) :
    (lkRootScale n).toReal = (n : ℝ)⁻¹ := by
  exact ENNReal.toReal_ofReal (inv_nonneg.mpr (Nat.cast_nonneg n))

private lemma lk_root_exponent (γ σ t : ℝ) (ν : Measure ℝ) {n : ℕ} (hn : n ≠ 0) :
    lkExponent (γ / (n : ℝ)) (lkRootSigma σ n) (lkRootMeasure n ν) t =
      lkExponent γ σ ν t / (n : ℝ) := by
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  unfold lkExponent lkRootMeasure
  rw [integral_smul_measure, lkRootScale_toReal, lkRootSigma_sq]
  simp only [Complex.real_smul]
  push_cast
  field_simp [hnR]

private lemma lk_exists_convolution_root {ν : Measure ℝ}
    (hν : ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂ν < ∞)
    (γ σ : ℝ) {n : ℕ} (hn : n ≠ 0) :
    ∃ ρ : ProbabilityMeasure ℝ,
      ∀ t : ℝ, charFun (ρ : Measure ℝ) t =
        Complex.exp (lkExponent γ σ ν t / (n : ℝ)) := by
  obtain ⟨ρ, hρ⟩ := lk_exists_probabilityMeasure_charFun (lk_root_moment hν n)
    (γ / (n : ℝ)) (lkRootSigma σ n)
  refine ⟨ρ, fun t ↦ ?_⟩
  rw [hρ, lk_root_exponent γ σ t ν hn]

private lemma lk_exp_div_pow (z : ℂ) {n : ℕ} (hn : n ≠ 0) :
    Complex.exp (z / (n : ℝ)) ^ n = Complex.exp z := by
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  field_simp [Nat.cast_ne_zero.mpr hn]

private lemma lk_infinitelyDivisible_of_charFun {μ ν : Measure ℝ}
    (hμ : IsProbabilityMeasure μ)
    (hν : ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂ν < ∞)
    (γ σ : ℝ) (hchar : ∀ t : ℝ, charFun μ t = Complex.exp (lkExponent γ σ ν t)) :
    ∀ n : ℕ, n ≠ 0 →
      ∃ ρ : Measure ℝ, IsProbabilityMeasure ρ ∧
        μ = Nat.iterate (Measure.conv ρ) (n - 1) ρ := by
  intro n hn
  obtain ⟨ρ, hρ⟩ := lk_exists_convolution_root hν γ σ hn
  have h_eq : μ = Measure.convPow (ρ : Measure ℝ) n := by
    let _ := Measure.isProbabilityMeasure_convPow (ν := (ρ : Measure ℝ)) n
    apply Measure.ext_of_charFun
    funext t
    rw [hchar, lk_charFun_convPow, hρ, lk_exp_div_pow _ hn]
  have h_pow := Measure.convPow_succ_eq_iterate (ν := (ρ : Measure ℝ)) (n - 1)
  rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn)] at h_pow
  exact ⟨ρ, inferInstance, h_eq.trans h_pow⟩

private noncomputable def lkSymmetrize (ρ : Measure ℝ) : Measure ℝ :=
  ρ ∗ ρ.map (-1 * ·)

private lemma lkSymmetrize_probability (ρ : Measure ℝ) [IsProbabilityMeasure ρ] :
    IsProbabilityMeasure (lkSymmetrize ρ) := by
  unfold lkSymmetrize
  infer_instance

private lemma lk_charFun_symmetrize (ρ : Measure ℝ) [IsProbabilityMeasure ρ] (t : ℝ) :
    charFun (lkSymmetrize ρ) t = ((‖charFun ρ t‖ ^ 2 : ℝ) : ℂ) := by
  unfold lkSymmetrize
  rw [charFun_conv, charFun_map_mul]
  rw [neg_one_mul, charFun_neg, Complex.mul_conj, Complex.normSq_eq_norm_sq]

private lemma lk_one_sub_cos_two_le (x : ℝ) :
    1 - Real.cos (2 * x) ≤ 4 * (1 - Real.cos x) := by
  rw [Real.cos_two_mul]
  nlinarith [sq_nonneg (Real.cos x - 1)]

private lemma lk_integrable_cos (ρ : Measure ℝ) [IsFiniteMeasure ρ] (t : ℝ) :
    Integrable (fun x : ℝ ↦ Real.cos (t * x)) ρ := by
  apply Integrable.of_bound (by fun_prop) 1
  exact ae_of_all ρ fun x ↦ by
    simpa [Real.norm_eq_abs] using Real.abs_cos_le_one (t * x)

private lemma lk_re_charFun_eq_integral_cos (ρ : Measure ℝ) [IsFiniteMeasure ρ] (t : ℝ) :
    (charFun ρ t).re = ∫ x, Real.cos (t * x) ∂ρ := by
  rw [charFun_apply_real]
  have h_exp : Integrable
      (fun x : ℝ ↦ Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I)) ρ := by
    apply Integrable.of_bound (by fun_prop) 1
    exact ae_of_all ρ fun x ↦ by
      rw [show (t : ℂ) * (x : ℂ) * Complex.I = ((t * x : ℝ) : ℂ) * Complex.I by
        push_cast
        ring]
      rw [Complex.norm_exp_ofReal_mul_I]
  calc
    (∫ x, Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) ∂ρ).re =
        ∫ x, (Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I)).re ∂ρ := by
      exact (integral_re h_exp).symm
    _ = ∫ x, Real.cos (t * x) ∂ρ := by
      apply integral_congr_ae
      exact ae_of_all ρ fun x ↦ by
        change (Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I)).re = Real.cos (t * x)
        rw [show (t : ℂ) * (x : ℂ) * Complex.I = ((t * x : ℝ) : ℂ) * Complex.I by
          push_cast
          ring]
        exact Complex.exp_ofReal_mul_I_re (t * x)

private lemma lk_one_sub_re_charFun_two_le (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    (t : ℝ) :
    1 - (charFun ρ (2 * t)).re ≤ 4 * (1 - (charFun ρ t).re) := by
  rw [lk_re_charFun_eq_integral_cos, lk_re_charFun_eq_integral_cos]
  have hcos₂ := lk_integrable_cos ρ (2 * t)
  have hcos := lk_integrable_cos ρ t
  calc
    1 - ∫ x, Real.cos ((2 * t) * x) ∂ρ =
        ∫ x, (1 - Real.cos ((2 * t) * x)) ∂ρ := by
      rw [integral_sub (integrable_const 1) hcos₂]
      simp
    _ ≤ ∫ x, 4 * (1 - Real.cos (t * x)) ∂ρ := by
      apply integral_mono ((integrable_const 1).sub hcos₂)
        ((integrable_const 1).sub hcos |>.const_mul 4)
      intro x
      change 1 - Real.cos ((2 * t) * x) ≤ 4 * (1 - Real.cos (t * x))
      simpa only [mul_assoc] using lk_one_sub_cos_two_le (t * x)
    _ = 4 * (1 - ∫ x, Real.cos (t * x) ∂ρ) := by
      rw [integral_const_mul, integral_sub (integrable_const 1) hcos]
      simp

private lemma lk_one_sub_norm_charFun_sq_two_le (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    (t : ℝ) :
    1 - ‖charFun ρ (2 * t)‖ ^ 2 ≤ 4 * (1 - ‖charFun ρ t‖ ^ 2) := by
  let _ := lkSymmetrize_probability ρ
  have h := lk_one_sub_re_charFun_two_le (lkSymmetrize ρ) t
  rw [lk_charFun_symmetrize, lk_charFun_symmetrize] at h
  simpa only [Complex.ofReal_re] using h

private lemma lk_exists_charFun_root {μ : Measure ℝ}
    (hID : ∀ n : ℕ, n ≠ 0 →
      ∃ ρ : Measure ℝ, IsProbabilityMeasure ρ ∧
        μ = Nat.iterate (Measure.conv ρ) (n - 1) ρ)
    {n : ℕ} (hn : n ≠ 0) :
    ∃ ρ : Measure ℝ, IsProbabilityMeasure ρ ∧
      ∀ t : ℝ, charFun μ t = charFun ρ t ^ n := by
  obtain ⟨ρ, hρ, hμ⟩ := hID n hn
  have h_pow := Measure.convPow_succ_eq_iterate (ν := ρ) (n - 1)
  rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn)] at h_pow
  refine ⟨ρ, hρ, fun t ↦ ?_⟩
  rw [hμ, ← h_pow, lk_charFun_convPow]

private lemma lk_charFun_ne_zero_double {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hID : ∀ n : ℕ, n ≠ 0 →
      ∃ ρ : Measure ℝ, IsProbabilityMeasure ρ ∧
        μ = Nat.iterate (Measure.conv ρ) (n - 1) ρ)
    {t : ℝ} (ht : charFun μ t ≠ 0) : charFun μ (2 * t) ≠ 0 := by
  have hpos : 0 < ‖charFun μ t‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr ht)
  obtain ⟨n, hnsmall⟩ := exists_pow_lt_of_lt_one hpos (show (3 / 4 : ℝ) < 1 by norm_num)
  have hnorm_le : ‖charFun μ t‖ ^ 2 ≤ 1 := by
    nlinarith [norm_nonneg (charFun μ t), norm_charFun_le_one (μ := μ) t]
  have hn : n ≠ 0 := by
    intro hn0
    subst n
    change 1 < ‖charFun μ t‖ ^ 2 at hnsmall
    exact (not_lt_of_ge hnorm_le) hnsmall
  obtain ⟨ρ, hρ, hroot⟩ := lk_exists_charFun_root hID hn
  have hnorm : ‖charFun μ t‖ = ‖charFun ρ t‖ ^ n := by
    rw [hroot t, norm_pow]
  have hsq : ‖charFun μ t‖ ^ 2 = (‖charFun ρ t‖ ^ 2) ^ n := by
    rw [hnorm, ← pow_mul, Nat.mul_comm, pow_mul]
  have hroot_large : (3 / 4 : ℝ) < ‖charFun ρ t‖ ^ 2 := by
    by_contra h
    have hp := pow_le_pow_left₀ (sq_nonneg ‖charFun ρ t‖) (le_of_not_gt h) n
    have hle : ‖charFun μ t‖ ^ 2 ≤ (3 / 4 : ℝ) ^ n := hsq.trans_le hp
    exact (not_lt_of_ge hle) hnsmall
  have hroot_double : charFun ρ (2 * t) ≠ 0 := by
    intro hzero
    have hineq := lk_one_sub_norm_charFun_sq_two_le ρ t
    rw [hzero, norm_zero] at hineq
    norm_num at hineq
    nlinarith
  rw [hroot (2 * t)]
  exact pow_ne_zero n hroot_double

private lemma lk_charFun_ne_zero_two_pow {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hID : ∀ n : ℕ, n ≠ 0 →
      ∃ ρ : Measure ℝ, IsProbabilityMeasure ρ ∧
        μ = Nat.iterate (Measure.conv ρ) (n - 1) ρ)
    {t : ℝ} (ht : charFun μ t ≠ 0) (m : ℕ) :
    charFun μ ((2 : ℝ) ^ m * t) ≠ 0 := by
  induction m with
  | zero => simpa using ht
  | succ m ih =>
      have heq : (2 : ℝ) ^ (m + 1) * t = 2 * ((2 : ℝ) ^ m * t) := by
        rw [pow_succ]
        ac_rfl
      rw [heq]
      exact lk_charFun_ne_zero_double hID ih

private lemma lk_charFun_ne_zero {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hID : ∀ n : ℕ, n ≠ 0 →
      ∃ ρ : Measure ℝ, IsProbabilityMeasure ρ ∧
        μ = Nat.iterate (Measure.conv ρ) (n - 1) ρ)
    (t : ℝ) : charFun μ t ≠ 0 := by
  have hlocal : ∀ᶠ x : ℝ in 𝓝 0, charFun μ x ≠ 0 := by
    have hopen : IsOpen ({0}ᶜ : Set ℂ) := isClosed_singleton.isOpen_compl
    have hmem : charFun μ 0 ∈ ({0}ᶜ : Set ℂ) := by simp
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using
      (MeasureTheory.continuous_charFun (μ := μ)).continuousAt.eventually
        (hopen.mem_nhds hmem)
  have hseq : Filter.Tendsto (fun m : ℕ ↦ t / (2 : ℝ) ^ m) Filter.atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, inv_pow, mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one
        (show 0 ≤ (2 : ℝ)⁻¹ by positivity) (show (2 : ℝ)⁻¹ < 1 by norm_num)).const_mul t
  obtain ⟨m, hm⟩ := (hseq.eventually hlocal).exists
  have h := lk_charFun_ne_zero_two_pow hID hm m
  have hpow : (2 : ℝ) ^ m ≠ 0 := pow_ne_zero m (by norm_num)
  have heq : (2 : ℝ) ^ m * (t / (2 : ℝ) ^ m) = t := by
    field_simp
  simpa only [heq] using h

private lemma lk_exists_distinguishedLog {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hID : ∀ n : ℕ, n ≠ 0 →
      ∃ ρ : Measure ℝ, IsProbabilityMeasure ρ ∧
        μ = Nat.iterate (Measure.conv ρ) (n - 1) ρ) :
    ∃ L : ℝ → ℂ, Continuous L ∧ L 0 = 0 ∧
      ∀ t : ℝ, Complex.exp (L t) = charFun μ t := by
  have hU : IsSimplyConnected (Set.univ : Set ℝ) :=
    (Homeomorph.Set.univ ℝ).toHomotopyEquiv.simplyConnectedSpace_iff.mpr inferInstance
  have hne : 0 ∉ charFun μ '' (Set.univ : Set ℝ) := by
    rintro ⟨t, -, ht⟩
    exact lk_charFun_ne_zero hID t ht
  obtain ⟨l, hl, hlexp⟩ := Complex.exists_continuousOn_eqOn_exp_comp hU isOpen_univ
    (MeasureTheory.continuous_charFun (μ := μ)).continuousOn hne
  have hlc : Continuous l := continuousOn_univ.mp hl
  have hlexp' (t : ℝ) : Complex.exp (l t) = charFun μ t := by
    simpa only [Function.comp_apply] using hlexp (Set.mem_univ t)
  let L : ℝ → ℂ := fun t ↦ l t - l 0
  refine ⟨L, hlc.sub continuous_const, by simp [L], fun t ↦ ?_⟩
  change Complex.exp (l t - l 0) = charFun μ t
  rw [Complex.exp_sub, hlexp' t, hlexp' 0]
  simp

private lemma lk_rootsOfUnity_finite {n : ℕ} (hn : n ≠ 0) :
    Set.Finite {z : ℂ | z ^ n = 1} := by
  let _ : NeZero n := ⟨hn⟩
  have hfin : Set.Finite
      (Set.range fun ζ : rootsOfUnity n ℂ ↦ (((ζ : ℂˣ) : ℂ))) := Set.finite_range _
  convert hfin using 1
  ext z
  constructor
  · intro hz
    exact ⟨rootsOfUnity.mkOfPowEq z hz, by simp⟩
  · rintro ⟨ζ, rfl⟩
    exact (mem_rootsOfUnity' n (ζ : ℂˣ)).mp ζ.property

private lemma lk_charFun_root_eq_exp_div {μ ρ : Measure ℝ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ρ]
    {L : ℝ → ℂ} (hL : Continuous L) (hL0 : L 0 = 0)
    (hLexp : ∀ t : ℝ, Complex.exp (L t) = charFun μ t)
    {n : ℕ} (hn : n ≠ 0)
    (hroot : ∀ t : ℝ, charFun μ t = charFun ρ t ^ n) :
    ∀ t : ℝ, charFun ρ t = Complex.exp (L t / (n : ℝ)) := by
  let q : ℝ → ℂ := fun t ↦ charFun ρ t / Complex.exp (L t / (n : ℝ))
  have hq : Continuous q := by
    unfold q
    have harg : Continuous (fun t : ℝ ↦ L t / (n : ℝ)) := by fun_prop
    have hden : Continuous (fun t : ℝ ↦ Complex.exp (L t / (n : ℝ))) :=
      (by fun_prop : Continuous Complex.exp).comp harg
    exact (MeasureTheory.continuous_charFun (μ := ρ)).div hden
      (fun t ↦ Complex.exp_ne_zero (L t / (n : ℝ)))
  have hmaps : Set.MapsTo q Set.univ {z : ℂ | z ^ n = 1} := by
    intro t _
    change q t ^ n = 1
    unfold q
    rw [div_pow, ← hroot t, lk_exp_div_pow _ hn, ← hLexp t]
    exact div_self (Complex.exp_ne_zero _)
  intro t
  have hconst := PreconnectedSpace.isPreconnected_univ.constant_of_mapsTo
    (lk_rootsOfUnity_finite hn).isDiscrete hq.continuousOn hmaps
    (Set.mem_univ t) (Set.mem_univ 0)
  have hq0 : q 0 = 1 := by simp [q, hL0]
  have hqt : q t = 1 := hconst.trans hq0
  exact (div_eq_one_iff_eq (Complex.exp_ne_zero (L t / (n : ℝ)))).mp hqt

private lemma lk_exists_exp_root {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hID : ∀ n : ℕ, n ≠ 0 →
      ∃ ρ : Measure ℝ, IsProbabilityMeasure ρ ∧
        μ = Nat.iterate (Measure.conv ρ) (n - 1) ρ)
    {L : ℝ → ℂ} (hL : Continuous L) (hL0 : L 0 = 0)
    (hLexp : ∀ t : ℝ, Complex.exp (L t) = charFun μ t)
    {n : ℕ} (hn : n ≠ 0) :
    ∃ ρ : Measure ℝ, IsProbabilityMeasure ρ ∧
      ∀ t : ℝ, charFun ρ t = Complex.exp (L t / (n : ℝ)) := by
  obtain ⟨ρ, hρ, hroot⟩ := lk_exists_charFun_root hID hn
  exact ⟨ρ, hρ, lk_charFun_root_eq_exp_div hL hL0 hLexp hn hroot⟩

private lemma lk_nat_mul_exp_div_sub_one_tendsto (z : ℂ) :
    Filter.Tendsto
      (fun n : ℕ ↦ ((n + 1 : ℕ) : ℂ) *
        (Complex.exp (z / ((n + 1 : ℕ) : ℂ)) - 1))
      Filter.atTop (𝓝 z) := by
  by_cases hz : z = 0
  · subst z
    simp
  · let u : ℕ → ℂ := fun n ↦ z / ((n + 1 : ℕ) : ℂ)
    have hinv : Filter.Tendsto (fun n : ℕ ↦ (((n + 1 : ℕ) : ℂ))⁻¹)
        Filter.atTop (𝓝 0) := by
      have h := (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℂ)).comp
        (Filter.tendsto_add_atTop_nat 1)
      exact h.congr' <| Filter.Eventually.of_forall fun n ↦ by rfl
    have hu : Filter.Tendsto u Filter.atTop (𝓝 0) := by
      unfold u
      simpa only [div_eq_mul_inv, mul_zero] using tendsto_const_nhds.mul hinv
    have hune : ∀ᶠ n : ℕ in Filter.atTop, u n ∈ ({0}ᶜ : Set ℂ) :=
      Filter.Eventually.of_forall fun n ↦ by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff, u]
        exact div_ne_zero hz (by exact_mod_cast Nat.succ_ne_zero n)
    have hu' : Filter.Tendsto u Filter.atTop (𝓝[≠] (0 : ℂ)) :=
      tendsto_nhdsWithin_iff.mpr ⟨hu, hune⟩
    have hslope := (Complex.hasDerivAt_exp 0).tendsto_slope_zero.comp hu'
    have hmul := hslope.const_mul z
    have hmul' : Filter.Tendsto
        (fun n ↦ z * (u n)⁻¹ * (Complex.exp (u n) - 1)) Filter.atTop (𝓝 z) := by
      simpa only [Function.comp_apply, zero_add, Complex.exp_zero, smul_eq_mul,
        mul_assoc, mul_one] using hmul
    refine hmul'.congr' (Filter.Eventually.of_forall fun n ↦ ?_)
    dsimp only [u, slope]
    have hn : (((n + 1 : ℕ) : ℂ)) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    field_simp [hz, hn]

private lemma lk_scaled_charFun_sub_one_tendsto {ρ : ℕ → Measure ℝ} {L : ℝ → ℂ}
    (hρ : ∀ n t, charFun (ρ n) t = Complex.exp (L t / ((n + 1 : ℕ) : ℝ)))
    (t : ℝ) :
    Filter.Tendsto
      (fun n : ℕ ↦ ((n + 1 : ℕ) : ℂ) * (charFun (ρ n) t - 1))
      Filter.atTop (𝓝 (L t)) := by
  refine (lk_nat_mul_exp_div_sub_one_tendsto (L t)).congr'
    (Filter.Eventually.of_forall fun n ↦ ?_)
  dsimp only
  rw [hρ n t]
  push_cast
  rfl

private lemma lk_sinc_le_cos_half {x : ℝ} (hx0 : 0 ≤ x) (hx2 : x ≤ 2) :
    Real.sinc x ≤ Real.cos (x / 2) := by
  rcases hx0.eq_or_lt with rfl | hx
  · simp
  rw [Real.sinc_of_ne_zero hx.ne']
  have hhalf0 : 0 ≤ x / 2 := by positivity
  have hhalfpi : x / 2 ≤ Real.pi / 2 := by linarith [Real.two_le_pi]
  have hcos : 0 ≤ Real.cos (x / 2) :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hhalfpi⟩
  have hsin : Real.sin (x / 2) ≤ x / 2 := Real.sin_le hhalf0
  have hid : Real.sin x = 2 * Real.sin (x / 2) * Real.cos (x / 2) := by
    calc
      Real.sin x = Real.sin (2 * (x / 2)) := by congr 1; ring
      _ = 2 * Real.sin (x / 2) * Real.cos (x / 2) := Real.sin_two_mul _
  rw [hid]
  apply (div_le_iff₀ hx).2
  nlinarith

private lemma lk_sq_div_32_le_one_sub_sinc_of_abs_le_two {x : ℝ} (hx : |x| ≤ 2) :
    x ^ 2 / 32 ≤ 1 - Real.sinc x := by
  wlog hx0 : 0 ≤ x generalizing x
  · have hneg : 0 ≤ -x := neg_nonneg.mpr (le_of_not_ge hx0)
    have habs : |-x| ≤ 2 := by simpa using hx
    simpa [Real.sinc_neg] using this habs hneg
  have hsinc : Real.sinc x ≤ Real.cos (x / 2) :=
    lk_sinc_le_cos_half hx0 (by simpa [abs_of_nonneg hx0] using hx)
  have harg : |x / 2| ≤ Real.pi := by
    rw [abs_div]
    norm_num
    nlinarith [Real.two_le_pi]
  have hcos := Real.cos_le_one_sub_mul_cos_sq harg
  have hpi : Real.pi ^ 2 ≤ 16 := by nlinarith [Real.pi_pos, Real.pi_le_four]
  have hpipos : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
  have hcoeff : (1 : ℝ) / 32 ≤ 1 / (2 * Real.pi ^ 2) := by
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    nlinarith
  calc
    x ^ 2 / 32 = x ^ 2 * (1 / 32) := by ring
    _ ≤ x ^ 2 * (1 / (2 * Real.pi ^ 2)) :=
      mul_le_mul_of_nonneg_left hcoeff (sq_nonneg x)
    _ = 2 / Real.pi ^ 2 * (x / 2) ^ 2 := by
      field_simp [ne_of_gt Real.pi_pos]
    _ ≤ 1 - Real.cos (x / 2) := by linarith
    _ ≤ 1 - Real.sinc x := by linarith

private noncomputable def lkCanonicalWeight (x : ℝ) : ℝ := x ^ 2 / (1 + x ^ 2)

private lemma lkCanonicalWeight_nonneg (x : ℝ) : 0 ≤ lkCanonicalWeight x := by
  unfold lkCanonicalWeight
  positivity

private lemma lkCanonicalWeight_le_one (x : ℝ) : lkCanonicalWeight x ≤ 1 := by
  unfold lkCanonicalWeight
  apply (div_le_one (by positivity : 0 < 1 + x ^ 2)).2
  linarith

private lemma lk_canonicalWeight_div_32_le_one_sub_sinc (x : ℝ) :
    lkCanonicalWeight x / 32 ≤ 1 - Real.sinc x := by
  by_cases hx : |x| ≤ 2
  · have hw : lkCanonicalWeight x ≤ x ^ 2 := by
      unfold lkCanonicalWeight
      apply (div_le_iff₀ (by positivity : 0 < 1 + x ^ 2)).2
      nlinarith [sq_nonneg x, sq_nonneg (x ^ 2)]
    calc
      lkCanonicalWeight x / 32 ≤ x ^ 2 / 32 := by gcongr
      _ ≤ 1 - Real.sinc x := lk_sq_div_32_le_one_sub_sinc_of_abs_le_two hx
  · have hx2 : 2 < |x| := lt_of_not_ge hx
    have hx0 : x ≠ 0 := fun h ↦ by norm_num [h] at hx2
    have hsinc : Real.sinc x ≤ (2 : ℝ)⁻¹ :=
      (Real.sinc_le_inv_abs hx0).trans (inv_anti₀ (by norm_num) hx2.le)
    have hw : lkCanonicalWeight x ≤ 1 := lkCanonicalWeight_le_one x
    calc
      lkCanonicalWeight x / 32 ≤ 1 / 32 := by gcongr
      _ ≤ 1 - Real.sinc x := by norm_num at hsinc ⊢; linarith

private lemma lk_scaled_exp_sub_one_bound (z : ℂ) (n : ℕ) :
    ‖((n + 1 : ℕ) : ℂ) * (Complex.exp (z / ((n + 1 : ℕ) : ℂ)) - 1)‖ ≤
      ‖z‖ * Real.exp ‖z‖ := by
  let d : ℝ := (n + 1 : ℕ)
  have hd : 0 < d := by dsimp [d]; positivity
  have hrem := Complex.norm_exp_sub_sum_le_norm_mul_exp (z / (d : ℂ)) 1
  norm_num [Finset.sum_range_succ] at hrem
  calc
    ‖((n + 1 : ℕ) : ℂ) * (Complex.exp (z / (d : ℂ)) - 1)‖ =
        d * ‖Complex.exp (z / (d : ℂ)) - 1‖ := by
          rw [Complex.norm_mul, Complex.norm_natCast]
    _ ≤ d * ((‖z‖ / d) * Real.exp (‖z‖ / d)) := by
          rw [abs_of_pos hd] at hrem
          exact mul_le_mul_of_nonneg_left hrem hd.le
    _ = ‖z‖ * Real.exp (‖z‖ / d) := by field_simp
    _ ≤ ‖z‖ * Real.exp ‖z‖ := by
      gcongr
      exact div_le_self (norm_nonneg z) (by dsimp [d]; norm_num)

private lemma lk_scaled_one_sub_charFun_bound {ρ : Measure ℝ} {L : ℝ → ℂ}
    (n : ℕ) (hρ : ∀ t, charFun ρ t = Complex.exp (L t / ((n + 1 : ℕ) : ℝ)))
    (t : ℝ) :
    ‖((n + 1 : ℕ) : ℂ) * (1 - charFun ρ t)‖ ≤ ‖L t‖ * Real.exp ‖L t‖ := by
  rw [hρ t]
  have h := lk_scaled_exp_sub_one_bound (L t) n
  rw [show 1 - Complex.exp (L t / ((n + 1 : ℕ) : ℝ)) =
      -(Complex.exp (L t / ((n + 1 : ℕ) : ℂ)) - 1) by
        push_cast
        ring]
  simpa only [mul_neg, norm_neg] using h

private lemma lk_norm_integral_scaled_one_sub_charFun_le {ρ : Measure ℝ} {L : ℝ → ℂ}
    (hL : Continuous L) (n : ℕ)
    (hρ : ∀ t, charFun ρ t = Complex.exp (L t / ((n + 1 : ℕ) : ℝ)))
    (a b : ℝ) (hab : a ≤ b) :
    ‖∫ t : ℝ in a..b, ((n + 1 : ℕ) : ℂ) * (1 - charFun ρ t)‖ ≤
      ∫ t : ℝ in a..b, ‖L t‖ * Real.exp ‖L t‖ := by
  apply intervalIntegral.norm_integral_le_of_norm_le hab
  · exact Filter.Eventually.of_forall fun t _ ↦ lk_scaled_one_sub_charFun_bound n hρ t
  · exact (by fun_prop : Continuous fun t ↦ ‖L t‖ * Real.exp ‖L t‖).intervalIntegrable _ _

private lemma lk_integral_one_sub_charFun (ρ : Measure ℝ) (hρ : IsProbabilityMeasure ρ) :
    ∫ t : ℝ in (-1)..1, (1 - charFun ρ t) =
      (2 : ℂ) * ((∫ x : ℝ, 1 - Real.sinc x ∂ρ : ℝ) : ℂ) := by
  rw [intervalIntegral.integral_sub]
  · rw [integral_charFun_Icc (μ := ρ) (r := 1) (by norm_num)]
    simp only [one_mul]
    rw [integral_sub (integrable_const _) Real.integrable_sinc]
    norm_num
    ring
  · exact intervalIntegrable_const
  · exact (continuous_charFun (μ := ρ)).intervalIntegrable _ _

private lemma lk_integral_one_sub_sinc_nonneg (ρ : Measure ℝ) :
    0 ≤ ∫ x : ℝ, 1 - Real.sinc x ∂ρ :=
  integral_nonneg fun x ↦ sub_nonneg.mpr (Real.sinc_le_one x)

private lemma lk_scaled_sinc_integral_le {ρ : Measure ℝ} {L : ℝ → ℂ}
    (hprob : IsProbabilityMeasure ρ) (hL : Continuous L) (n : ℕ)
    (hρ : ∀ t, charFun ρ t = Complex.exp (L t / ((n + 1 : ℕ) : ℝ))) :
    (n + 1 : ℝ) * ∫ x : ℝ, 1 - Real.sinc x ∂ρ ≤
      (1 / 2 : ℝ) * ∫ t : ℝ in (-1)..1, ‖L t‖ * Real.exp ‖L t‖ := by
  have hnorm := lk_norm_integral_scaled_one_sub_charFun_le hL n hρ (-1) 1 (by norm_num)
  have heq : (∫ t : ℝ in (-1)..1,
      ((n + 1 : ℕ) : ℂ) * (1 - charFun ρ t)) =
      ((n + 1 : ℕ) : ℂ) * ((2 : ℂ) *
        ((∫ x : ℝ, 1 - Real.sinc x ∂ρ : ℝ) : ℂ)) := by
    rw [intervalIntegral.integral_const_mul]
    rw [lk_integral_one_sub_charFun ρ hprob]
  rw [heq] at hnorm
  have hnon := lk_integral_one_sub_sinc_nonneg ρ
  simp only [Complex.norm_mul, Complex.norm_natCast, Complex.norm_two, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hnon] at hnorm
  push_cast at hnorm
  nlinarith

private noncomputable def lkCanonicalWeightNN (x : ℝ) : ℝ≥0 :=
  ⟨lkCanonicalWeight x, lkCanonicalWeight_nonneg x⟩

@[simp]
private lemma lk_coe_canonicalWeightNN (x : ℝ) :
    (lkCanonicalWeightNN x : ℝ) = lkCanonicalWeight x := rfl

private lemma lk_canonicalWeightNN_le_one (x : ℝ) :
    (lkCanonicalWeightNN x : ℝ≥0∞) ≤ 1 := by
  rw [← ENNReal.coe_one]
  apply ENNReal.coe_le_coe.mpr
  exact_mod_cast lkCanonicalWeight_le_one x

private noncomputable def lkCanonicalBase (ρ : Measure ℝ) (hρ : IsProbabilityMeasure ρ) :
    FiniteMeasure ℝ := by
  letI := hρ
  let m := ρ.withDensity fun x ↦ (lkCanonicalWeightNN x : ℝ≥0∞)
  have hm : IsFiniteMeasure m := by
    apply isFiniteMeasure_withDensity
    apply (lt_of_le_of_lt (b := ∫⁻ _ : ℝ in Set.univ, (1 : ℝ≥0∞) ∂ρ) ?_
      (by
        rw [lintegral_one, Measure.restrict_univ]
        exact measure_lt_top ρ Set.univ)).ne
    simpa only [Measure.restrict_univ, lintegral_one] using
      (lintegral_mono lk_canonicalWeightNN_le_one :
        (∫⁻ x, (lkCanonicalWeightNN x : ℝ≥0∞) ∂ρ) ≤ ∫⁻ _ : ℝ, (1 : ℝ≥0∞) ∂ρ)
  exact ⟨m, hm⟩

private noncomputable def lkCanonicalMeasure (ρ : Measure ℝ)
    (hρ : IsProbabilityMeasure ρ) (n : ℕ) : FiniteMeasure ℝ :=
  (n + 1 : ℝ≥0) • lkCanonicalBase ρ hρ

private lemma lk_canonicalBase_le (ρ : Measure ℝ) (hρ : IsProbabilityMeasure ρ) :
    (lkCanonicalBase ρ hρ : Measure ℝ) ≤ ρ := by
  change ρ.withDensity (fun x ↦ (lkCanonicalWeightNN x : ℝ≥0∞)) ≤ ρ
  simpa using withDensity_mono (μ := ρ)
    (ae_of_all ρ fun x ↦ lk_canonicalWeightNN_le_one x)

private lemma lk_canonicalMeasure_apply_le (ρ : Measure ℝ) (hρ : IsProbabilityMeasure ρ)
    (n : ℕ) (s : Set ℝ) :
    ((lkCanonicalMeasure ρ hρ n s : ℝ≥0) : ℝ) ≤
      (n + 1 : ℝ) * ρ.real s := by
  rw [lkCanonicalMeasure, FiniteMeasure.smul_apply]
  change (((n + 1 : ℝ≥0) * lkCanonicalBase ρ hρ s : ℝ≥0) : ℝ) ≤ _
  push_cast
  gcongr
  rw [← FiniteMeasure.measureReal_eq_coe_coeFn]
  rw [Measure.real, Measure.real]
  exact ENNReal.toReal_mono (measure_ne_top ρ s) ((lk_canonicalBase_le ρ hρ) s)

private lemma lk_canonicalBase_mass (ρ : Measure ℝ) (hρ : IsProbabilityMeasure ρ) :
    ((lkCanonicalBase ρ hρ).mass : ℝ) = ∫ x, lkCanonicalWeight x ∂ρ := by
  rw [show ((lkCanonicalBase ρ hρ).mass : ℝ) =
      (ρ.withDensity (fun x ↦ (lkCanonicalWeightNN x : ℝ≥0∞))).real Set.univ by rfl]
  rw [Measure.real, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hint : Integrable (fun x ↦ (lkCanonicalWeightNN x : ℝ)) ρ := by
    apply (integrable_const (c := (1 : ℝ))).mono
    · exact (by
        simpa only [lk_coe_canonicalWeightNN] using (show Continuous lkCanonicalWeight by
          unfold lkCanonicalWeight
          exact (continuous_id.pow 2).div₀ (continuous_const.add (continuous_id.pow 2))
            fun x : ℝ ↦ by positivity)
        : Continuous fun x : ℝ ↦ (lkCanonicalWeightNN x : ℝ)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun x ↦ by
        change |lkCanonicalWeight x| ≤ |(1 : ℝ)|
        simpa [abs_of_nonneg (lkCanonicalWeight_nonneg x)] using lkCanonicalWeight_le_one x
  rw [lintegral_coe_eq_integral _ hint, ENNReal.toReal_ofReal]
  · rfl
  · exact integral_nonneg fun x ↦ lkCanonicalWeight_nonneg x

private lemma lk_canonicalMeasure_mass (ρ : Measure ℝ) (hρ : IsProbabilityMeasure ρ)
    (n : ℕ) :
    ((lkCanonicalMeasure ρ hρ n).mass : ℝ) =
      (n + 1 : ℝ) * ∫ x, lkCanonicalWeight x ∂ρ := by
  rw [lkCanonicalMeasure, FiniteMeasure.mass, FiniteMeasure.smul_apply]
  simp only [smul_eq_mul, NNReal.coe_mul]
  rw [← FiniteMeasure.mass, lk_canonicalBase_mass]
  push_cast
  rfl

private lemma lk_canonicalWeight_integrable (ρ : Measure ℝ) (hρ : IsProbabilityMeasure ρ) :
    Integrable lkCanonicalWeight ρ := by
  apply (integrable_const (c := (1 : ℝ))).mono
  · exact (show Continuous lkCanonicalWeight by
      unfold lkCanonicalWeight
      exact (continuous_id.pow 2).div₀ (continuous_const.add (continuous_id.pow 2))
        fun x : ℝ ↦ by positivity).aestronglyMeasurable
  · exact ae_of_all ρ fun x ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (lkCanonicalWeight_nonneg x), norm_one]
      exact lkCanonicalWeight_le_one x

private lemma lk_integral_canonicalWeight_le_sinc (ρ : Measure ℝ)
    (hρ : IsProbabilityMeasure ρ) :
    ∫ x, lkCanonicalWeight x ∂ρ ≤ 32 * ∫ x, 1 - Real.sinc x ∂ρ := by
  rw [← integral_const_mul]
  apply integral_mono (lk_canonicalWeight_integrable ρ hρ)
    ((integrable_const _).sub Real.integrable_sinc |>.const_mul 32)
  intro x
  change lkCanonicalWeight x ≤ 32 * (1 - Real.sinc x)
  nlinarith [lk_canonicalWeight_div_32_le_one_sub_sinc x]

private lemma lk_canonicalMeasure_mass_le {ρ : Measure ℝ} {L : ℝ → ℂ}
    (hprob : IsProbabilityMeasure ρ) (hL : Continuous L) (n : ℕ)
    (hρ : ∀ t, charFun ρ t = Complex.exp (L t / ((n + 1 : ℕ) : ℝ))) :
    ((lkCanonicalMeasure ρ hprob n).mass : ℝ) ≤
      16 * ∫ t : ℝ in (-1)..1, ‖L t‖ * Real.exp ‖L t‖ := by
  rw [lk_canonicalMeasure_mass]
  have hw := lk_integral_canonicalWeight_le_sinc ρ hprob
  have hs := lk_scaled_sinc_integral_le hprob hL n hρ
  calc
    (n + 1 : ℝ) * ∫ x, lkCanonicalWeight x ∂ρ ≤
        (n + 1 : ℝ) * (32 * ∫ x, 1 - Real.sinc x ∂ρ) := by gcongr
    _ = 32 * ((n + 1 : ℝ) * ∫ x, 1 - Real.sinc x ∂ρ) := by ring
    _ ≤ 32 * ((1 / 2 : ℝ) *
        ∫ t : ℝ in (-1)..1, ‖L t‖ * Real.exp ‖L t‖) := by gcongr
    _ = 16 * ∫ t : ℝ in (-1)..1, ‖L t‖ * Real.exp ‖L t‖ := by ring

private noncomputable def lkCanonicalMassBound (L : ℝ → ℂ) : ℝ≥0 :=
  ⟨16 * ∫ t : ℝ in (-1)..1, ‖L t‖ * Real.exp ‖L t‖, by
    apply mul_nonneg (by norm_num)
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro t _
    positivity⟩

private lemma lk_canonicalMeasure_mass_le_bound {ρ : Measure ℝ} {L : ℝ → ℂ}
    (hprob : IsProbabilityMeasure ρ) (hL : Continuous L) (n : ℕ)
    (hρ : ∀ t, charFun ρ t = Complex.exp (L t / ((n + 1 : ℕ) : ℝ))) :
    (lkCanonicalMeasure ρ hprob n).mass ≤ lkCanonicalMassBound L := by
  apply NNReal.coe_le_coe.mp
  change ((lkCanonicalMeasure ρ hprob n).mass : ℝ) ≤
    16 * ∫ t : ℝ in (-1)..1, ‖L t‖ * Real.exp ‖L t‖
  exact lk_canonicalMeasure_mass_le hprob hL n hρ

private lemma lk_canonicalMeasure_tail_le {ρ : Measure ℝ} {L : ℝ → ℂ}
    (hprob : IsProbabilityMeasure ρ) (hL : Continuous L) (n : ℕ)
    (hρ : ∀ t, charFun ρ t = Complex.exp (L t / ((n + 1 : ℕ) : ℝ)))
    {r : ℝ} (hr : 0 < r) :
    ((lkCanonicalMeasure ρ hprob n {x | r < |x|} : ℝ≥0) : ℝ) ≤
      (1 / 2 : ℝ) * r *
        ∫ t : ℝ in (-2 * r⁻¹)..(2 * r⁻¹), ‖L t‖ * Real.exp ‖L t‖ := by
  have htail := measureReal_abs_gt_le_integral_charFun (μ := ρ) hr
  have htail' : ρ.real {x | r < |x|} ≤ (1 / 2 : ℝ) * r *
      ‖∫ t : ℝ in (-2 * r⁻¹)..(2 * r⁻¹), 1 - charFun ρ t‖ := by
    norm_num at htail ⊢
    exact htail
  have hab : -2 * r⁻¹ ≤ 2 * r⁻¹ := by
    have := inv_pos.mpr hr
    linarith
  have hnorm := lk_norm_integral_scaled_one_sub_charFun_le hL n hρ
    (-2 * r⁻¹) (2 * r⁻¹) hab
  have hscale :
      ‖∫ t : ℝ in (-2 * r⁻¹)..(2 * r⁻¹),
        ((n + 1 : ℕ) : ℂ) * (1 - charFun ρ t)‖ =
      (n + 1 : ℝ) * ‖∫ t : ℝ in (-2 * r⁻¹)..(2 * r⁻¹), 1 - charFun ρ t‖ := by
    rw [intervalIntegral.integral_const_mul, Complex.norm_mul, Complex.norm_natCast]
    push_cast
    rfl
  rw [hscale] at hnorm
  calc
    ((lkCanonicalMeasure ρ hprob n {x | r < |x|} : ℝ≥0) : ℝ) ≤
        (n + 1 : ℝ) * ρ.real {x | r < |x|} :=
      lk_canonicalMeasure_apply_le ρ hprob n _
    _ ≤ (n + 1 : ℝ) * ((1 / 2 : ℝ) * r *
        ‖∫ t : ℝ in (-2 * r⁻¹)..(2 * r⁻¹), 1 - charFun ρ t‖) := by gcongr
    _ = (1 / 2 : ℝ) * r * ((n + 1 : ℝ) *
        ‖∫ t : ℝ in (-2 * r⁻¹)..(2 * r⁻¹), 1 - charFun ρ t‖) := by ring
    _ ≤ (1 / 2 : ℝ) * r *
        ∫ t : ℝ in (-2 * r⁻¹)..(2 * r⁻¹), ‖L t‖ * Real.exp ‖L t‖ := by gcongr

private lemma lk_canonicalMeasure_tight_bound {ρ : ℕ → Measure ℝ} {L : ℝ → ℂ}
    (hprob : ∀ n, IsProbabilityMeasure (ρ n)) (hL : Continuous L) (hL0 : L 0 = 0)
    (hρ : ∀ n t, charFun (ρ n) t = Complex.exp (L t / ((n + 1 : ℕ) : ℝ)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ r > 0, ∀ n,
      ((lkCanonicalMeasure (ρ n) (hprob n) n {x | r < |x|} : ℝ≥0) : ℝ) ≤ ε := by
  let g : ℝ → ℝ := fun t ↦ ‖L t‖ * Real.exp ‖L t‖
  have hg : Continuous g := by
    dsimp only [g]
    fun_prop
  have hg0 : g 0 = 0 := by simp [g, hL0]
  obtain ⟨δ, hδ, hclose⟩ :=
    (Metric.continuousAt_iff.mp (hg.continuousAt : ContinuousAt g 0))
      (ε / 2) (by positivity)
  let r : ℝ := 4 / δ
  have hr : 0 < r := by dsimp [r]; positivity
  have hradius : 2 * r⁻¹ = δ / 2 := by
    dsimp [r]
    field_simp
    norm_num
  refine ⟨r, hr, fun n ↦ ?_⟩
  have hab : -2 * r⁻¹ ≤ 2 * r⁻¹ := by
    have := inv_pos.mpr hr
    linarith
  have hg_bound : ∀ t ∈ Set.Icc (-2 * r⁻¹) (2 * r⁻¹), g t ≤ ε / 2 := by
    intro t ht
    apply le_of_lt
    have htδ : dist t 0 < δ := by
      rw [Real.dist_eq, sub_zero]
      change (-2 * r⁻¹ ≤ t ∧ t ≤ 2 * r⁻¹) at ht
      have habst : |t| ≤ 2 * r⁻¹ := (abs_le).2 ⟨by linarith [ht.1], ht.2⟩
      rw [hradius] at habst
      nlinarith [abs_nonneg t]
    simpa [hg0, Real.dist_eq, abs_of_nonneg (by positivity : 0 ≤ g t)] using hclose htδ
  have hint : (∫ t : ℝ in (-2 * r⁻¹)..(2 * r⁻¹), g t) ≤
      ∫ _ : ℝ in (-2 * r⁻¹)..(2 * r⁻¹), ε / 2 :=
    intervalIntegral.integral_mono_on hab (hg.intervalIntegrable _ _)
      intervalIntegrable_const hg_bound
  rw [intervalIntegral.integral_const] at hint
  have htail := lk_canonicalMeasure_tail_le (hprob n) hL n (hρ n) hr
  change ((lkCanonicalMeasure (ρ n) (hprob n) n {x | r < |x|} : ℝ≥0) : ℝ) ≤ ε
  change _ ≤ (1 / 2 : ℝ) * r * (∫ t : ℝ in (-2 * r⁻¹)..(2 * r⁻¹), g t) at htail
  have hlen : 2 * r⁻¹ - -2 * r⁻¹ = 4 / r := by field_simp; ring
  rw [hlen, smul_eq_mul] at hint
  calc
    ((lkCanonicalMeasure (ρ n) (hprob n) n {x | r < |x|} : ℝ≥0) : ℝ) ≤
        (1 / 2 : ℝ) * r * (∫ t : ℝ in (-2 * r⁻¹)..(2 * r⁻¹), g t) := htail
    _ ≤ (1 / 2 : ℝ) * r * (4 / r * (ε / 2)) := by gcongr
    _ = ε := by field_simp; ring

private lemma lk_exists_canonical_limit {ρ : ℕ → Measure ℝ} {L : ℝ → ℂ}
    (hprob : ∀ n, IsProbabilityMeasure (ρ n)) (hL : Continuous L) (hL0 : L 0 = 0)
    (hρ : ∀ n t, charFun (ρ n) t = Complex.exp (L t / ((n + 1 : ℕ) : ℝ))) :
    ∃ K : FiniteMeasure ℝ, ∃ U : Ultrafilter ℕ, (U : Filter ℕ) ≤ Filter.atTop ∧
      Filter.Tendsto
        (fun n ↦ lkCanonicalMeasure (ρ n) (hprob n) n) U (𝓝 K) := by
  let u : ℕ → ℝ≥0 := fun m ↦ 1 / ((m : ℝ≥0) + 1)
  have hu : Filter.Tendsto u Filter.atTop (𝓝 0) := by
    simpa only [u] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ≥0))
  have hex (m : ℕ) : ∃ r > 0, ∀ n,
      ((lkCanonicalMeasure (ρ n) (hprob n) n {x | r < |x|} : ℝ≥0) : ℝ) ≤
        (u m : ℝ) := by
    apply lk_canonicalMeasure_tight_bound hprob hL hL0 hρ
    dsimp only [u]
    positivity
  let r : ℕ → ℝ := fun m ↦ Classical.choose (hex m)
  have hr (m : ℕ) : 0 < r m := (Classical.choose_spec (hex m)).1
  have htail (m n : ℕ) :
      ((lkCanonicalMeasure (ρ n) (hprob n) n {x | r m < |x|} : ℝ≥0) : ℝ) ≤
        (u m : ℝ) :=
    (Classical.choose_spec (hex m)).2 n
  let C : ℝ≥0 := lkCanonicalMassBound L
  let A : ℕ → Set ℝ := fun m ↦ Set.Icc (-(r m)) (r m)
  have hA (m : ℕ) : IsCompact (A m) := isCompact_Icc
  let Kseq : ℕ → FiniteMeasure ℝ := fun n ↦
    lkCanonicalMeasure (ρ n) (hprob n) n
  have hmem (n : ℕ) : Kseq n ∈
      {K : FiniteMeasure ℝ | K.mass ≤ C ∧ ∀ m, K (A m)ᶜ ≤ u m} := by
    constructor
    · exact lk_canonicalMeasure_mass_le_bound (hprob n) hL n (hρ n)
    · intro m
      have hset : (A m)ᶜ = {x : ℝ | r m < |x|} := by
        ext x
        simp only [A, Set.mem_compl_iff, Set.mem_Icc, not_and_or, Set.mem_ofPred_eq]
        rw [lt_abs]
        grind
      rw [hset]
      apply NNReal.coe_le_coe.mp
      change ((lkCanonicalMeasure (ρ n) (hprob n) n {x | r m < |x|} : ℝ≥0) : ℝ) ≤
        (u m : ℝ)
      exact htail m n
  have hcompact := isCompact_setOfPred_finiteMeasure_mass_le_compl_isCompact_le
    C hu hA (Or.inl (inferInstance : NormalSpace ℝ))
  obtain ⟨K, -, hcluster⟩ := hcompact.exists_mapClusterPt
    (f := Filter.atTop) (u := Kseq)
    (Filter.tendsto_principal.mpr (Filter.Eventually.of_forall hmem))
  obtain ⟨U, hU, hconv⟩ := mapClusterPt_iff_ultrafilter.mp hcluster
  refine ⟨K, U, hU, ?_⟩
  simpa only [Kseq] using hconv

private noncomputable def lkTaylorRemainder (t : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (Complex.I * (t : ℂ) * z) - 1 - Complex.I * (t : ℂ) * z

private noncomputable def lkSecondSlope (t : ℝ) : ℂ → ℂ :=
  (Function.swap dslope (0 : ℂ))^[2] (lkTaylorRemainder t)

private lemma lk_taylorRemainder_analytic (t : ℝ) (z : ℂ) :
    AnalyticAt ℂ (lkTaylorRemainder t) z := by
  unfold lkTaylorRemainder
  fun_prop

private lemma lk_secondSlope_continuous (t : ℝ) : Continuous (lkSecondSlope t) := by
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hz : z = 0
  · subst z
    exact (lk_taylorRemainder_analytic t 0).hasFPowerSeriesAt
      |>.has_fpower_series_iterate_dslope_fslope 2 |>.continuousAt
  · rw [lkSecondSlope, show (Function.swap dslope (0 : ℂ))^[2] (lkTaylorRemainder t) =
        dslope (dslope (lkTaylorRemainder t) 0) 0 by rfl]
    apply (continuousAt_dslope_of_ne hz).2
    exact (continuousAt_dslope_of_ne hz).2 (lk_taylorRemainder_analytic t z).continuousAt

@[simp]
private lemma lk_taylorRemainder_zero (t : ℝ) : lkTaylorRemainder t 0 = 0 := by
  simp [lkTaylorRemainder]

private lemma lk_deriv_taylorRemainder_zero (t : ℝ) :
    deriv (lkTaylorRemainder t) 0 = 0 := by
  unfold lkTaylorRemainder
  simp (disch := fun_prop)

private lemma lk_secondSlope_mul_sq (t : ℝ) (z : ℂ) :
    z ^ 2 * lkSecondSlope t z = lkTaylorRemainder t z := by
  have h := pow_sub_smul_iterate_dslope_of_zero
    (f := lkTaylorRemainder t) (a := (0 : ℂ)) 2 (fun k hk ↦ ?_) z
  · simpa [lkSecondSlope, lk_taylorRemainder_zero t] using h
  · have hk' : k = 0 ∨ k = 1 := by omega
    rcases hk' with rfl | rfl
    · simp [lk_taylorRemainder_zero t]
    · simp [lk_deriv_taylorRemainder_zero t]

private lemma lk_secondSlope_of_ne (t : ℝ) {z : ℂ} (hz : z ≠ 0) :
    lkSecondSlope t z = lkTaylorRemainder t z / z ^ 2 := by
  apply (eq_div_iff (pow_ne_zero 2 hz)).2
  simpa [mul_comm] using lk_secondSlope_mul_sq t z

@[simp]
private lemma lk_secondSlope_zero (t : ℝ) :
    lkSecondSlope t 0 = -((t : ℂ) ^ 2) / 2 := by
  have hp := (lk_taylorRemainder_analytic t 0).hasFPowerSeriesAt
  have h := (hp.has_fpower_series_iterate_dslope_fslope 2).coeff_zero
    (fun _ ↦ (1 : ℂ))
  rw [show (Function.swap dslope (0 : ℂ))^[2] (lkTaylorRemainder t) =
    lkSecondSlope t by rfl] at h
  rw [← h]
  suffices iteratedDeriv 2 (lkTaylorRemainder t) 0 = -((t : ℂ) ^ 2) by simp [this]
  let a : ℂ := Complex.I * (t : ℂ)
  let f : ℂ → ℂ := fun z ↦ Complex.exp (a * z)
  let c : ℂ → ℂ := fun _ ↦ 1
  let l : ℂ → ℂ := fun z ↦ a * z
  change iteratedDeriv 2 (fun z ↦ (f z - c z) - l z) 0 = -((t : ℂ) ^ 2)
  have hfd : ContDiffAt ℂ 2 f 0 := by dsimp only [f]; fun_prop
  have hcd : ContDiffAt ℂ 2 c 0 := by dsimp only [c]; fun_prop
  have hld : ContDiffAt ℂ 2 l 0 := by dsimp only [l]; fun_prop
  have hsplit : iteratedDeriv 2 (fun z ↦ (f z - c z) - l z) 0 =
      (iteratedDeriv 2 f 0 - iteratedDeriv 2 c 0) - iteratedDeriv 2 l 0 := by
    calc
      _ = iteratedDeriv 2 (fun z ↦ f z - c z) 0 - iteratedDeriv 2 l 0 :=
        iteratedDeriv_sub (hfd.sub hcd) hld
      _ = _ := by
        congr 1
        exact iteratedDeriv_sub hfd hcd
  rw [hsplit]
  have hf : iteratedDeriv 2 f 0 = a ^ 2 := by
    rw [show iteratedDeriv 2 f = fun z ↦ a ^ 2 * Complex.exp (a * z) from
      iteratedDeriv_cexp_const_mul 2 a]
    simp
  have hc : iteratedDeriv 2 c 0 = 0 := by
    dsimp only [c]
    rw [iteratedDeriv_const]
    norm_num
  have hl : iteratedDeriv 2 l 0 = 0 := by
    rw [show l = fun z ↦ a * id z by rfl, iteratedDeriv_const_mul a (by fun_prop)]
    rw [iteratedDeriv_id]
    norm_num
  rw [hf, hc, hl, sub_zero]
  dsimp only [a]
  rw [mul_pow, Complex.I_sq]
  ring

private noncomputable def lkSmoothJump (t x : ℝ) : ℂ :=
  Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)) - 1 -
    Complex.I * (t : ℂ) * (x : ℂ) / ((1 + x ^ 2 : ℝ) : ℂ)

private noncomputable def lkCanonicalIntegrand (t x : ℝ) : ℂ :=
  ((1 + x ^ 2 : ℝ) : ℂ) * lkSecondSlope t (x : ℂ) +
    Complex.I * (t : ℂ) * (x : ℂ)

private lemma lk_canonicalIntegrand_continuous (t : ℝ) :
    Continuous (lkCanonicalIntegrand t) := by
  unfold lkCanonicalIntegrand
  exact ((by fun_prop : Continuous fun x : ℝ ↦ ((1 + x ^ 2 : ℝ) : ℂ)).mul
    ((lk_secondSlope_continuous t).comp (by fun_prop))).add (by fun_prop)

@[simp]
private lemma lk_canonicalIntegrand_zero (t : ℝ) :
    lkCanonicalIntegrand t 0 = -((t : ℂ) ^ 2) / 2 := by
  simp [lkCanonicalIntegrand]

private lemma lk_weight_mul_canonicalIntegrand (t x : ℝ) :
    (lkCanonicalWeight x : ℂ) * lkCanonicalIntegrand t x = lkSmoothJump t x := by
  by_cases hx : x = 0
  · subst x
    simp [lkCanonicalWeight, lkCanonicalIntegrand, lkSmoothJump]
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx
  have hd : (1 + (x : ℂ) ^ 2) ≠ 0 := by
    exact_mod_cast (by positivity : (1 + x ^ 2 : ℝ) ≠ 0)
  rw [lkCanonicalIntegrand, lk_secondSlope_of_ne t hxC]
  unfold lkTaylorRemainder lkSmoothJump lkCanonicalWeight
  push_cast
  field_simp [hxC, hd]
  ring_nf

private lemma lk_norm_secondSlope_le_of_abs_le_one (t : ℝ) {x : ℝ} (hx : |x| ≤ 1) :
    ‖lkSecondSlope t (x : ℂ)‖ ≤ t ^ 2 * Real.exp |t| := by
  by_cases hx0 : x = 0
  · subst x
    change ‖lkSecondSlope t 0‖ ≤ t ^ 2 * Real.exp |t|
    have hexp : Real.exp |t| ≥ 1 := Real.one_le_exp (abs_nonneg t)
    rw [lk_secondSlope_zero]
    norm_num [sq_abs]
    nlinarith [sq_nonneg t]
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx0
  rw [lk_secondSlope_of_ne t hxC]
  rw [norm_div, Complex.norm_pow, Complex.norm_real, Real.norm_eq_abs]
  have hrem := Complex.norm_exp_sub_sum_le_norm_mul_exp
    (Complex.I * (t : ℂ) * (x : ℂ)) 2
  norm_num [Finset.sum_range_succ] at hrem
  change ‖Complex.exp (Complex.I * ↑t * ↑x) - 1 - Complex.I * ↑t * ↑x‖ /
    |x| ^ 2 ≤ t ^ 2 * Real.exp |t|
  have hxabs : 0 < |x| := abs_pos.mpr hx0
  have hrem' : ‖Complex.exp (Complex.I * ↑t * ↑x) - 1 - Complex.I * ↑t * ↑x‖ ≤
      (|t| * |x|) ^ 2 * Real.exp (|t| * |x|) := by
    calc
      _ = ‖Complex.exp (Complex.I * ↑t * ↑x) - (1 + Complex.I * ↑t * ↑x)‖ := by
        congr 1
        ring
      _ ≤ _ := hrem
  calc
    ‖Complex.exp (Complex.I * ↑t * ↑x) - 1 - Complex.I * ↑t * ↑x‖ / |x| ^ 2 ≤
        ((|t| * |x|) ^ 2 * Real.exp (|t| * |x|)) / |x| ^ 2 := by gcongr
    _ = t ^ 2 * Real.exp (|t| * |x|) := by
      rw [mul_pow, sq_abs]
      field_simp
    _ ≤ t ^ 2 * Real.exp |t| := by
      gcongr
      exact mul_le_of_le_one_right (abs_nonneg t) hx

private lemma lk_norm_canonicalIntegrand_le (t x : ℝ) :
    ‖lkCanonicalIntegrand t x‖ ≤
      max (2 * t ^ 2 * Real.exp |t| + |t|) (4 + 2 * |t|) := by
  by_cases hx : |x| ≤ 1
  · calc
      ‖lkCanonicalIntegrand t x‖ ≤
          |1 + x ^ 2| * ‖lkSecondSlope t (x : ℂ)‖ + |t| * |x| := by
        unfold lkCanonicalIntegrand
        calc
          _ ≤ ‖((1 + x ^ 2 : ℝ) : ℂ) * lkSecondSlope t (x : ℂ)‖ +
              ‖Complex.I * (t : ℂ) * (x : ℂ)‖ := norm_add_le _ _
          _ = _ := by
            simp only [Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs,
              Complex.norm_I, one_mul]
      _ ≤ 2 * (t ^ 2 * Real.exp |t|) + |t| := by
        have hx2 : x ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one x).2 hx
        have hq := lk_norm_secondSlope_le_of_abs_le_one t hx
        have hxnon : 0 ≤ x ^ 2 := sq_nonneg x
        have hone : |1 + x ^ 2| ≤ 2 := by
          rw [abs_of_nonneg (by linarith : 0 ≤ 1 + x ^ 2)]
          linarith
        exact add_le_add
          (mul_le_mul hone hq (norm_nonneg _) (by positivity))
          (by simpa only [mul_one] using
            mul_le_mul_of_nonneg_left hx (abs_nonneg t))
      _ = 2 * t ^ 2 * Real.exp |t| + |t| := by ring
      _ ≤ max (2 * t ^ 2 * Real.exp |t| + |t|) (4 + 2 * |t|) := le_max_left _ _
  · have hx1 : 1 < |x| := lt_of_not_ge hx
    have hw : (1 / 2 : ℝ) ≤ lkCanonicalWeight x := by
      unfold lkCanonicalWeight
      rw [le_div_iff₀ (by positivity : 0 < 1 + x ^ 2)]
      have hx2 : 1 < x ^ 2 := by rw [← sq_abs]; nlinarith
      nlinarith
    have hjump : ‖lkSmoothJump t x‖ ≤ 2 + |t| := by
      unfold lkSmoothJump
      calc
        ‖Complex.exp (Complex.I * ↑t * ↑x) - 1 -
            Complex.I * ↑t * ↑x / ((1 + x ^ 2 : ℝ) : ℂ)‖ ≤
            ‖Complex.exp (Complex.I * ↑t * ↑x) - 1‖ +
              ‖Complex.I * ↑t * ↑x / ((1 + x ^ 2 : ℝ) : ℂ)‖ := norm_sub_le _ _
        _ ≤ 2 + |t| := by
          have hexp : ‖Complex.exp (Complex.I * ↑t * ↑x) - 1‖ ≤ 2 := by
            calc
              _ ≤ ‖Complex.exp (Complex.I * ↑t * ↑x)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
              _ = 2 := by
                rw [show Complex.I * (t : ℂ) * (x : ℂ) =
                    ((t * x : ℝ) : ℂ) * Complex.I by
                  push_cast
                  ring]
                rw [Complex.norm_exp_ofReal_mul_I]
                norm_num [Complex.norm_def]
          have hfrac : ‖Complex.I * ↑t * ↑x /
              ((1 + x ^ 2 : ℝ) : ℂ)‖ ≤ |t| := by
            simp only [norm_div, Complex.norm_mul, Complex.norm_I, one_mul,
              Complex.norm_real, Real.norm_eq_abs]
            rw [abs_of_nonneg (by positivity : 0 ≤ 1 + x ^ 2)]
            apply (div_le_iff₀ (by positivity : 0 < 1 + x ^ 2)).2
            have hxle : |x| ≤ 1 + x ^ 2 := by nlinarith [abs_nonneg x, sq_abs x]
            nlinarith [abs_nonneg t]
          linarith
    have hweight : 0 < lkCanonicalWeight x :=
      (by norm_num : 0 < (1 / 2 : ℝ)).trans_le hw
    have heq := congrArg norm (lk_weight_mul_canonicalIntegrand t x)
    simp only [Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hweight] at heq
    calc
      ‖lkCanonicalIntegrand t x‖ = ‖lkSmoothJump t x‖ / lkCanonicalWeight x := by
        rw [← heq]
        field_simp
      _ ≤ (2 + |t|) / (1 / 2 : ℝ) :=
        div_le_div₀ (by positivity) hjump (by norm_num) hw
      _ = 4 + 2 * |t| := by ring
      _ ≤ max (2 * t ^ 2 * Real.exp |t| + |t|) (4 + 2 * |t|) := le_max_right _ _

private noncomputable def lkCanonicalIntegrandBCF (t : ℝ) :
    BoundedContinuousFunction ℝ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (lkCanonicalIntegrand t)
    (lk_canonicalIntegrand_continuous t)
    (max (2 * t ^ 2 * Real.exp |t| + |t|) (4 + 2 * |t|))
    (lk_norm_canonicalIntegrand_le t)

private noncomputable def lkCanonicalIntegrandReBCF (t : ℝ) :
    BoundedContinuousFunction ℝ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x ↦ (lkCanonicalIntegrand t x).re)
    (Complex.continuous_re.comp (lk_canonicalIntegrand_continuous t))
    (max (2 * t ^ 2 * Real.exp |t| + |t|) (4 + 2 * |t|)) fun x ↦
      (Complex.abs_re_le_norm _).trans (lk_norm_canonicalIntegrand_le t x)

private noncomputable def lkCanonicalIntegrandImBCF (t : ℝ) :
    BoundedContinuousFunction ℝ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x ↦ (lkCanonicalIntegrand t x).im)
    (Complex.continuous_im.comp (lk_canonicalIntegrand_continuous t))
    (max (2 * t ^ 2 * Real.exp |t| + |t|) (4 + 2 * |t|)) fun x ↦
      (Complex.abs_im_le_norm _).trans (lk_norm_canonicalIntegrand_le t x)

private lemma lk_tendsto_integral_canonicalIntegrand
    {M : ℕ → FiniteMeasure ℝ} {K : FiniteMeasure ℝ} {F : Filter ℕ}
    (hM : Filter.Tendsto M F (nhds K)) (t : ℝ) :
    Filter.Tendsto
      (fun n ↦ ∫ x, lkCanonicalIntegrand t x ∂(M n : Measure ℝ)) F
      (nhds (∫ x, lkCanonicalIntegrand t x ∂(K : Measure ℝ))) := by
  have hre := (FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hM)
    (lkCanonicalIntegrandReBCF t)
  have him := (FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hM)
    (lkCanonicalIntegrandImBCF t)
  have hsum := hre.ofReal.add (him.ofReal.mul_const Complex.I)
  convert hsum using 1
  · funext n
    change (∫ x, lkCanonicalIntegrand t x ∂(M n : Measure ℝ)) =
      ((∫ x, (lkCanonicalIntegrand t x).re ∂(M n : Measure ℝ) : ℝ) : ℂ) +
        (∫ x, (lkCanonicalIntegrand t x).im ∂(M n : Measure ℝ) : ℝ) * Complex.I
    exact (integral_re_add_im
      ((lkCanonicalIntegrandBCF t).integrable (M n : Measure ℝ))).symm
  · congr 1
    change (∫ x, lkCanonicalIntegrand t x ∂(K : Measure ℝ)) =
      ((∫ x, (lkCanonicalIntegrand t x).re ∂(K : Measure ℝ) : ℝ) : ℂ) +
        (∫ x, (lkCanonicalIntegrand t x).im ∂(K : Measure ℝ) : ℝ) * Complex.I
    exact (integral_re_add_im
      ((lkCanonicalIntegrandBCF t).integrable (K : Measure ℝ))).symm

private noncomputable def lkSmoothTruncation (x : ℝ) : ℝ :=
  x / (1 + x ^ 2)

private lemma lk_smoothTruncation_continuous : Continuous lkSmoothTruncation := by
  unfold lkSmoothTruncation
  exact continuous_id.div₀ (continuous_const.add (continuous_id.pow 2)) fun x ↦ by positivity

private lemma lk_abs_smoothTruncation_le_one (x : ℝ) :
    |lkSmoothTruncation x| ≤ 1 := by
  unfold lkSmoothTruncation
  rw [abs_div, abs_of_nonneg (by positivity : 0 ≤ 1 + x ^ 2)]
  apply (div_le_iff₀ (by positivity : 0 < 1 + x ^ 2)).2
  nlinarith [abs_nonneg x, sq_abs x]

private lemma lk_smoothTruncation_integrable (rho : Measure ℝ) [IsFiniteMeasure rho] :
    Integrable lkSmoothTruncation rho := by
  apply Integrable.of_bound lk_smoothTruncation_continuous.aestronglyMeasurable 1
  exact ae_of_all rho fun x ↦ by
    simpa only [Real.norm_eq_abs, norm_one] using lk_abs_smoothTruncation_le_one x

private lemma lk_smoothJump_integrable (rho : Measure ℝ) [IsFiniteMeasure rho] (t : ℝ) :
    Integrable (lkSmoothJump t) rho := by
  have hlinear : Integrable
      (fun x ↦ Complex.I * (t : ℂ) * (lkSmoothTruncation x : ℂ)) rho :=
    (lk_smoothTruncation_integrable rho).ofReal.const_mul (Complex.I * (t : ℂ))
  have hlinear' : Integrable
      (fun x : ℝ ↦ Complex.I * (t : ℂ) * (x : ℂ) /
        ((1 + x ^ 2 : ℝ) : ℂ)) rho := by
    convert hlinear using 1
    funext x
    unfold lkSmoothTruncation
    push_cast
    ring
  exact ((lk_integrable_exp_mul_I rho t).sub (integrable_const 1)).sub hlinear'

private noncomputable def lkDrift (rho : Measure ℝ) (n : ℕ) : ℝ :=
  (n + 1 : ℝ) * ∫ x, lkSmoothTruncation x ∂rho

private lemma lk_integral_canonicalMeasure (rho : Measure ℝ)
    (hprob : IsProbabilityMeasure rho) (n : ℕ) (t : ℝ) :
    (∫ x, lkCanonicalIntegrand t x ∂(lkCanonicalMeasure rho hprob n : Measure ℝ)) =
      ((n + 1 : ℕ) : ℂ) * ∫ x, lkSmoothJump t x ∂rho := by
  rw [lkCanonicalMeasure]
  change (∫ x, lkCanonicalIntegrand t x ∂
      ((n + 1 : ℝ≥0) • (lkCanonicalBase rho hprob : Measure ℝ))) = _
  rw [integral_smul_nnreal_measure]
  change ((n + 1 : ℝ≥0) : ℝ) •
      (∫ x, lkCanonicalIntegrand t x ∂rho.withDensity
        (fun x ↦ (lkCanonicalWeightNN x : ℝ≥0∞))) = _
  rw [show (fun x ↦ (lkCanonicalWeightNN x : ℝ≥0∞)) =
      fun x ↦ ((lkCanonicalWeightNN x : ℝ≥0) : ℝ≥0∞) by rfl]
  have hweight : Measurable lkCanonicalWeightNN := by
    apply Continuous.measurable
    rw [show lkCanonicalWeightNN = fun x ↦ Real.toNNReal (lkCanonicalWeight x) by
      funext x
      rw [Real.toNNReal_of_nonneg (lkCanonicalWeight_nonneg x)]
      rfl]
    apply continuous_real_toNNReal.comp
    unfold lkCanonicalWeight
    exact (continuous_id.pow 2).div₀ (continuous_const.add (continuous_id.pow 2)) fun x : ℝ ↦ by
      positivity
  rw [integral_withDensity_eq_integral_smul hweight]
  simp only [NNReal.smul_def, Complex.real_smul]
  rw [show (∫ x, (lkCanonicalWeightNN x : ℝ) * lkCanonicalIntegrand t x ∂rho) =
      ∫ x, lkSmoothJump t x ∂rho by
        apply integral_congr_ae
        exact ae_of_all rho fun x ↦ lk_weight_mul_canonicalIntegrand t x]
  push_cast
  rfl

private lemma lk_scaled_charFun_eq_drift_add_canonical (rho : Measure ℝ)
    (hprob : IsProbabilityMeasure rho) (n : ℕ) (t : ℝ) :
    ((n + 1 : ℕ) : ℂ) * (charFun rho t - 1) =
      Complex.I * (t : ℂ) * (lkDrift rho n : ℂ) +
        ∫ x, lkCanonicalIntegrand t x ∂(lkCanonicalMeasure rho hprob n : Measure ℝ) := by
  have hchar : charFun rho t - 1 =
      ∫ x, Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)) - 1 ∂rho := by
    rw [charFun_apply_real]
    rw [show (fun x : ℝ ↦ Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I)) =
        fun x : ℝ ↦ Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)) by
      funext x
      congr 1
      ring]
    rw [integral_sub (lk_integrable_exp_mul_I rho t) (integrable_const 1), integral_const]
    simp
  have hsplit : (∫ x, Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)) - 1 ∂rho) =
      Complex.I * (t : ℂ) * (∫ x, lkSmoothTruncation x ∂rho : ℝ) +
        ∫ x, lkSmoothJump t x ∂rho := by
    have hlinear : Complex.I * (t : ℂ) * (∫ x, lkSmoothTruncation x ∂rho : ℝ) =
        ∫ x, Complex.I * (t : ℂ) * (lkSmoothTruncation x : ℂ) ∂rho := by
      rw [integral_const_mul, integral_complex_ofReal]
    rw [hlinear]
    calc
      (∫ x, Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)) - 1 ∂rho) =
          ∫ x, Complex.I * (t : ℂ) * (lkSmoothTruncation x : ℂ) +
            lkSmoothJump t x ∂rho := by
        apply integral_congr_ae
        exact ae_of_all rho fun x ↦ by
          unfold lkSmoothJump lkSmoothTruncation
          push_cast
          ring
      _ = _ := integral_add
        ((lk_smoothTruncation_integrable rho).ofReal.const_mul (Complex.I * (t : ℂ)))
        (lk_smoothJump_integrable rho t)
  rw [hchar, hsplit, mul_add, lk_integral_canonicalMeasure rho hprob n t]
  unfold lkDrift
  push_cast
  ring

private lemma lk_tendsto_drift {rho : ℕ → Measure ℝ} {L : ℝ → ℂ}
    (hprob : ∀ n, IsProbabilityMeasure (rho n))
    (hroot : ∀ n t, charFun (rho n) t =
      Complex.exp (L t / ((n + 1 : ℕ) : ℝ)))
    {K : FiniteMeasure ℝ} {U : Ultrafilter ℕ}
    (hU : (U : Filter ℕ) ≤ Filter.atTop)
    (hK : Filter.Tendsto
      (fun n ↦ lkCanonicalMeasure (rho n) (hprob n) n) U (nhds K)) :
    Filter.Tendsto (fun n ↦ lkDrift (rho n) n) U
      (nhds ((L 1 - ∫ x, lkCanonicalIntegrand 1 x ∂(K : Measure ℝ)).im)) := by
  have hscaled := (lk_scaled_charFun_sub_one_tendsto hroot 1).mono_left hU
  have hint := lk_tendsto_integral_canonicalIntegrand hK 1
  have hdiff := hscaled.sub hint
  have hI : Filter.Tendsto
      (fun n ↦ Complex.I * (lkDrift (rho n) n : ℂ)) U
      (nhds (L 1 - ∫ x, lkCanonicalIntegrand 1 x ∂(K : Measure ℝ))) := by
    convert hdiff using 1
    funext n
    rw [lk_scaled_charFun_eq_drift_add_canonical (rho n) (hprob n) n 1]
    push_cast
    ring
  have him := Complex.continuous_im.continuousAt.tendsto.comp hI
  have hfun : (Complex.im ∘ fun n ↦ Complex.I * (lkDrift (rho n) n : ℂ)) =
      fun n ↦ lkDrift (rho n) n := by
    funext n
    rw [Function.comp_apply, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [hfun, Complex.sub_im] at him
  exact him

private lemma lk_log_eq_drift_add_canonical {rho : ℕ → Measure ℝ} {L : ℝ → ℂ}
    (hprob : ∀ n, IsProbabilityMeasure (rho n))
    (hroot : ∀ n t, charFun (rho n) t =
      Complex.exp (L t / ((n + 1 : ℕ) : ℝ)))
    {K : FiniteMeasure ℝ} {U : Ultrafilter ℕ}
    (hU : (U : Filter ℕ) ≤ Filter.atTop)
    (hK : Filter.Tendsto
      (fun n ↦ lkCanonicalMeasure (rho n) (hprob n) n) U (nhds K)) :
    ∃ b : ℝ, ∀ t : ℝ, L t = Complex.I * (t : ℂ) * (b : ℂ) +
      ∫ x, lkCanonicalIntegrand t x ∂(K : Measure ℝ) := by
  let b : ℝ := (L 1 - ∫ x, lkCanonicalIntegrand 1 x ∂(K : Measure ℝ)).im
  have hb : Filter.Tendsto (fun n ↦ lkDrift (rho n) n) U (nhds b) :=
    lk_tendsto_drift hprob hroot hU hK
  refine ⟨b, fun t ↦ ?_⟩
  have hscaled := (lk_scaled_charFun_sub_one_tendsto hroot t).mono_left hU
  have hint := lk_tendsto_integral_canonicalIntegrand hK t
  have hdrift : Filter.Tendsto
      (fun n ↦ Complex.I * (t : ℂ) * (lkDrift (rho n) n : ℂ)) U
      (nhds (Complex.I * (t : ℂ) * (b : ℂ))) :=
    hb.ofReal.const_mul (Complex.I * (t : ℂ))
  have hrhs := hdrift.add hint
  have hscaled' : Filter.Tendsto
      (fun n ↦ Complex.I * (t : ℂ) * (lkDrift (rho n) n : ℂ) +
        ∫ x, lkCanonicalIntegrand t x ∂
          (lkCanonicalMeasure (rho n) (hprob n) n : Measure ℝ)) U
      (nhds (L t)) := by
    refine hscaled.congr' (Filter.Eventually.of_forall fun n ↦ ?_)
    exact lk_scaled_charFun_eq_drift_add_canonical (rho n) (hprob n) n t
  exact tendsto_nhds_unique hscaled' hrhs

private noncomputable def lkInverseCanonicalWeight (x : ℝ) : ℝ≥0∞ :=
  if x = 0 then 0 else ENNReal.ofReal ((1 + x ^ 2) / x ^ 2)

private lemma lk_inverseCanonicalWeight_measurable :
    Measurable lkInverseCanonicalWeight := by
  unfold lkInverseCanonicalWeight
  apply Measurable.ite (by simpa only [Set.ofPred_eq_eq_singleton] using
    (measurableSet_singleton (0 : ℝ)))
  · exact measurable_const
  · exact Measurable.ennreal_ofReal
      ((measurable_const.add (measurable_id.pow_const 2)).div (measurable_id.pow_const 2))

private lemma lk_inverseCanonicalWeight_lt_top (x : ℝ) :
    lkInverseCanonicalWeight x < ∞ := by
  unfold lkInverseCanonicalWeight
  split_ifs
  · exact ENNReal.zero_lt_top
  · exact ENNReal.ofReal_lt_top

private lemma lk_moment_mul_inverseCanonicalWeight_le (x : ℝ) :
    lkInverseCanonicalWeight x * ENNReal.ofReal (min 1 (x ^ 2)) ≤ 2 := by
  by_cases hx : x = 0
  · subst x
    simp [lkInverseCanonicalWeight]
  simp only [lkInverseCanonicalWeight, hx, ↓reduceIte]
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (1 + x ^ 2) / x ^ 2)]
  rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num]
  apply ENNReal.ofReal_le_ofReal
  by_cases hx1 : x ^ 2 ≤ 1
  · rw [min_eq_right hx1]
    have hx2 : x ^ 2 ≠ 0 := pow_ne_zero 2 hx
    field_simp
    linarith [sq_nonneg x]
  · rw [min_eq_left (le_of_not_ge hx1)]
    have hx2 : 0 < x ^ 2 := sq_pos_of_ne_zero hx
    rw [mul_one]
    apply (div_le_iff₀ hx2).2
    nlinarith

private noncomputable def lkLevyMeasure (K : FiniteMeasure ℝ) : Measure ℝ :=
  (K : Measure ℝ).withDensity lkInverseCanonicalWeight

private lemma lk_levyMeasure_zero (K : FiniteMeasure ℝ) :
    lkLevyMeasure K {0} = 0 := by
  rw [lkLevyMeasure, withDensity_apply _ (measurableSet_singleton 0)]
  simp [lkInverseCanonicalWeight]

private lemma lk_levyMeasure_moment (K : FiniteMeasure ℝ) :
    (∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂lkLevyMeasure K) < ∞ := by
  rw [lkLevyMeasure, lintegral_withDensity_eq_lintegral_mul _
    lk_inverseCanonicalWeight_measurable
    (by fun_prop : Measurable fun x : ℝ ↦ ENNReal.ofReal (min 1 (x ^ 2)))]
  calc
    (∫⁻ x, (lkInverseCanonicalWeight *
        fun x : ℝ ↦ ENNReal.ofReal (min 1 (x ^ 2))) x ∂(K : Measure ℝ)) ≤
        ∫⁻ _ : ℝ, (2 : ℝ≥0∞) ∂(K : Measure ℝ) :=
      lintegral_mono lk_moment_mul_inverseCanonicalWeight_le
    _ < ∞ := by
      rw [lintegral_const]
      exact ENNReal.mul_lt_top (by norm_num) (measure_lt_top (K : Measure ℝ) Set.univ)

private lemma lk_inverseCanonicalWeight_toReal_of_ne {x : ℝ} (hx : x ≠ 0) :
    (lkInverseCanonicalWeight x).toReal = (1 + x ^ 2) / x ^ 2 := by
  simp only [lkInverseCanonicalWeight, hx, ↓reduceIte]
  rw [ENNReal.toReal_ofReal]
  positivity

private lemma lk_inverse_mul_smoothJump {x t : ℝ} (hx : x ≠ 0) :
    ((lkInverseCanonicalWeight x).toReal : ℂ) * lkSmoothJump t x =
      lkCanonicalIntegrand t x := by
  rw [lk_inverseCanonicalWeight_toReal_of_ne hx]
  rw [← lk_weight_mul_canonicalIntegrand t x]
  unfold lkCanonicalWeight
  push_cast
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx
  have hd : (1 + (x : ℂ) ^ 2) ≠ 0 := by
    exact_mod_cast (by positivity : (1 + x ^ 2 : ℝ) ≠ 0)
  field_simp [hxC, hd]

private lemma lk_integral_smoothJump_levyMeasure (K : FiniteMeasure ℝ) (t : ℝ) :
    (∫ x, lkSmoothJump t x ∂lkLevyMeasure K) =
      ∫ x, lkCanonicalIntegrand t x ∂
        ((K : Measure ℝ).restrict ({0} : Set ℝ)ᶜ) := by
  rw [lkLevyMeasure, integral_withDensity_eq_integral_toReal_smul
    lk_inverseCanonicalWeight_measurable
    (ae_of_all (K : Measure ℝ) lk_inverseCanonicalWeight_lt_top)]
  rw [← integral_indicator (measurableSet_singleton 0).compl]
  apply integral_congr_ae
  exact ae_of_all (K : Measure ℝ) fun x ↦ by
    by_cases hx : x = 0
    · subst x
      simp [lkInverseCanonicalWeight]
    · rw [Set.indicator_of_mem (show x ∈ ({0} : Set ℝ)ᶜ by simpa)]
      change (lkInverseCanonicalWeight x).toReal • lkSmoothJump t x = _
      rw [Complex.real_smul]
      exact lk_inverse_mul_smoothJump hx

private lemma lk_integral_canonical_eq_atom_add_smooth
    (K : FiniteMeasure ℝ) (t : ℝ) :
    (∫ x, lkCanonicalIntegrand t x ∂(K : Measure ℝ)) =
      -(((K : Measure ℝ).real {0} : ℂ) * (t : ℂ) ^ 2 / 2) +
        ∫ x, lkSmoothJump t x ∂lkLevyMeasure K := by
  have hint : Integrable (lkCanonicalIntegrand t) (K : Measure ℝ) :=
    (lkCanonicalIntegrandBCF t).integrable (K : Measure ℝ)
  rw [← integral_add_compl (measurableSet_singleton 0) hint]
  rw [integral_singleton, lk_canonicalIntegrand_zero,
    lk_integral_smoothJump_levyMeasure]
  simp only [Complex.real_smul]
  ring

private noncomputable def lkDriftCorrection (x : ℝ) : ℝ :=
  Set.indicator {y : ℝ | |y| ≤ 1} id x - lkSmoothTruncation x

private lemma lk_abs_driftCorrection_le_moment (x : ℝ) :
    |lkDriftCorrection x| ≤ min 1 (x ^ 2) := by
  by_cases hx : |x| ≤ 1
  · rw [min_eq_right ((sq_le_one_iff_abs_le_one x).2 hx)]
    rw [lkDriftCorrection, Set.indicator_of_mem
      (show x ∈ {y : ℝ | |y| ≤ 1} from hx)]
    change |x - x / (1 + x ^ 2)| ≤ x ^ 2
    rw [show x - x / (1 + x ^ 2) = x ^ 3 / (1 + x ^ 2) by
      field_simp
      ring]
    rw [abs_div, abs_pow, abs_of_nonneg (by positivity : 0 ≤ 1 + x ^ 2)]
    apply (div_le_iff₀ (by positivity : 0 < 1 + x ^ 2)).2
    rw [← sq_abs x]
    nlinarith [abs_nonneg x, sq_nonneg (|x| ^ 2)]
  · have hx' : 1 < |x| := lt_of_not_ge hx
    rw [min_eq_left ((one_le_sq_iff_one_le_abs x).2 hx'.le)]
    rw [lkDriftCorrection, Set.indicator_of_notMem
      (show x ∉ {y : ℝ | |y| ≤ 1} from hx), zero_sub, abs_neg]
    exact lk_abs_smoothTruncation_le_one x

private lemma lk_driftCorrection_stronglyMeasurable :
    StronglyMeasurable lkDriftCorrection := by
  unfold lkDriftCorrection
  exact (stronglyMeasurable_id.indicator
    ((isClosed_le (by fun_prop) (by fun_prop)).measurableSet)).sub
      lk_smoothTruncation_continuous.stronglyMeasurable

private lemma lk_driftCorrection_integrable {nu : Measure ℝ}
    (hnu : ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂nu < ∞) :
    Integrable lkDriftCorrection nu := by
  exact (lk_moment_integrable hnu).mono'
    lk_driftCorrection_stronglyMeasurable.aestronglyMeasurable
    (ae_of_all nu fun x ↦ by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ min 1 (x ^ 2))]
        using lk_abs_driftCorrection_le_moment x)

private lemma lk_smoothJump_eq_jump_add_correction (t x : ℝ) :
    lkSmoothJump t x = Complex.I * (t : ℂ) * (lkDriftCorrection x : ℂ) +
      lkJump t x := by
  unfold lkSmoothJump lkJump lkDriftCorrection lkSmoothTruncation
  by_cases hx : |x| ≤ 1
  · simp only [Set.indicator_of_mem (s := {y : ℝ | |y| ≤ 1}) hx, id_eq]
    push_cast
    ring
  · simp only [Set.indicator_of_notMem (s := {y : ℝ | |y| ≤ 1}) hx]
    push_cast
    ring

private lemma lk_integral_smoothJump_eq_jump_add_correction {nu : Measure ℝ}
    (hnu : ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂nu < ∞) (t : ℝ) :
    (∫ x, lkSmoothJump t x ∂nu) =
      Complex.I * (t : ℂ) * (∫ x, lkDriftCorrection x ∂nu : ℝ) +
        ∫ x, lkJump t x ∂nu := by
  have hlinear : Complex.I * (t : ℂ) * (∫ x, lkDriftCorrection x ∂nu : ℝ) =
      ∫ x, Complex.I * (t : ℂ) * (lkDriftCorrection x : ℂ) ∂nu := by
    rw [integral_const_mul, integral_complex_ofReal]
  rw [hlinear]
  calc
    (∫ x, lkSmoothJump t x ∂nu) =
        ∫ x, Complex.I * (t : ℂ) * (lkDriftCorrection x : ℂ) + lkJump t x ∂nu := by
      apply integral_congr_ae
      exact ae_of_all nu fun x ↦ lk_smoothJump_eq_jump_add_correction t x
    _ = _ := integral_add
      ((lk_driftCorrection_integrable hnu).ofReal.const_mul (Complex.I * (t : ℂ)))
      (lk_jump_integrable hnu t)

private noncomputable def lkGaussianCoefficient (K : FiniteMeasure ℝ) : ℝ :=
  Real.sqrt ((K : Measure ℝ).real {0})

private lemma lk_gaussianCoefficient_nonneg (K : FiniteMeasure ℝ) :
    0 ≤ lkGaussianCoefficient K := Real.sqrt_nonneg _

private lemma lk_gaussianCoefficient_sq (K : FiniteMeasure ℝ) :
    lkGaussianCoefficient K ^ 2 = (K : Measure ℝ).real {0} := by
  exact Real.sq_sqrt (measureReal_nonneg)

private lemma lk_canonical_triplet {L : ℝ → ℂ} (K : FiniteMeasure ℝ) (b : ℝ)
    (hL : ∀ t : ℝ, L t = Complex.I * (t : ℂ) * (b : ℂ) +
      ∫ x, lkCanonicalIntegrand t x ∂(K : Measure ℝ)) :
    ∃ gamma : ℝ, ∃ sigma : ℝ, 0 ≤ sigma ∧
      ∃ nu : Measure ℝ, nu {0} = 0 ∧
        (∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂nu < ∞) ∧
          ∀ t : ℝ, L t = lkExponent gamma sigma nu t := by
  let nu := lkLevyMeasure K
  let c : ℝ := ∫ x, lkDriftCorrection x ∂nu
  let gamma := b + c
  let sigma := lkGaussianCoefficient K
  have hnu : ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂nu < ∞ :=
    lk_levyMeasure_moment K
  refine ⟨gamma, sigma, lk_gaussianCoefficient_nonneg K, nu,
    lk_levyMeasure_zero K, hnu, fun t ↦ ?_⟩
  rw [hL t, lk_integral_canonical_eq_atom_add_smooth,
    lk_integral_smoothJump_eq_jump_add_correction hnu,
    ← lk_gaussianCoefficient_sq K]
  unfold lkExponent gamma c sigma
  push_cast
  ring

private lemma lk_exists_root_sequence {mu : Measure ℝ} [IsProbabilityMeasure mu]
    (hID : ∀ n : ℕ, n ≠ 0 →
      ∃ rho : Measure ℝ, IsProbabilityMeasure rho ∧
        mu = Nat.iterate (Measure.conv rho) (n - 1) rho)
    {L : ℝ → ℂ} (hL : Continuous L) (hL0 : L 0 = 0)
    (hLexp : ∀ t : ℝ, Complex.exp (L t) = charFun mu t) :
    ∃ rho : ℕ → Measure ℝ, (∀ n, IsProbabilityMeasure (rho n)) ∧
      ∀ n t, charFun (rho n) t =
        Complex.exp (L t / ((n + 1 : ℕ) : ℝ)) := by
  choose rho hprob hroot using fun n ↦
    lk_exists_exp_root hID hL hL0 hLexp (Nat.succ_ne_zero n)
  exact ⟨rho, hprob, hroot⟩

private lemma lk_triplet_of_infinitelyDivisible {mu : Measure ℝ}
    [IsProbabilityMeasure mu]
    (hID : ∀ n : ℕ, n ≠ 0 →
      ∃ rho : Measure ℝ, IsProbabilityMeasure rho ∧
        mu = Nat.iterate (Measure.conv rho) (n - 1) rho) :
    ∃ gamma : ℝ, ∃ sigma : ℝ, 0 ≤ sigma ∧
      ∃ nu : Measure ℝ, nu {0} = 0 ∧
        (∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂nu < ∞) ∧
          ∀ t : ℝ, charFun mu t = Complex.exp (lkExponent gamma sigma nu t) := by
  obtain ⟨L, hL, hL0, hLexp⟩ := lk_exists_distinguishedLog hID
  obtain ⟨rho, hprob, hroot⟩ := lk_exists_root_sequence hID hL hL0 hLexp
  obtain ⟨K, U, hU, hK⟩ := lk_exists_canonical_limit hprob hL hL0 hroot
  obtain ⟨b, hrep⟩ := lk_log_eq_drift_add_canonical hprob hroot hU hK
  obtain ⟨gamma, sigma, hsigma, nu, hnu0, hnu, htrip⟩ :=
    lk_canonical_triplet K b hrep
  refine ⟨gamma, sigma, hsigma, nu, hnu0, hnu, fun t ↦ ?_⟩
  rw [← hLexp t, htrip t]

/-- **Lévy–Khintchin representation on the real line.** A probability measure $\mu$ on
$\mathbb{R}$ is infinitely divisible, meaning that for every integer $n \ge 1$ there is a
probability measure $\rho$ on $\mathbb{R}$ whose $n$-fold convolution power $\rho^{\ast n}$
equals $\mu$, if and only if there are real numbers $\gamma$ and $\sigma \ge 0$ and a measure
$\nu$ on $\mathbb{R}$ with $\nu(\{0\}) = 0$ and
$\int \min(1, x^2)\, d\nu(x) < \infty$ such that the characteristic function $\hat\mu$ of $\mu$
satisfies, for every $t \in \mathbb{R}$,
$$
\hat\mu(t) = \exp\Big(i \gamma t - \frac{\sigma^2 t^2}{2} +
\int_{\mathbb{R}} \big(e^{itx} - 1 - itx \, \mathbf{1}_{\{|x| \le 1\}}(x)\big) \, d\nu(x)\Big).
$$

Proof: The reverse implication uses compound Poisson approximation plus Lévy continuity; the
forward implication uses a distinguished logarithm, canonical measures, and Prokhorov compactness.
For the equivalence, see William Feller, *An Introduction to Probability Theory and Its
Applications*, vol. II, Theorem XVII.2.1.

Proves `Wanted` entry `levy_Khintchin`.

Source: Ken-iti Sato, *Lévy Processes and Infinitely Divisible Distributions*,
Cambridge Studies in Advanced Mathematics 68, Cambridge University Press (1999),
Theorem 8.1, pp. 37–38, ISBN 978-0-521-55302-5.
<https://books.google.com/books?vid=ISBN9780521553025&jscmd=SearchWithinVolume2&q=Theorem+8.1>
Scope: restricts Sato Theorem 8.1 (stated for `ℝ^d`) to `ℝ`, and formalizes
only the existence direction (i), omitting uniqueness of the generating
triplet (ii). The jump integrand uses the hard truncation `x * 1_{|x| ≤ 1}`,
which is an equivalent convention to Sato's `x / (1 + |x|^2)` after
reparameterizing the drift `γ`.
-/
theorem levy_Khintchin :
    ∀ (μ : MeasureTheory.Measure ℝ), MeasureTheory.IsProbabilityMeasure μ →
      (MeasureTheory.Measure.IsInfinitelyDivisible μ ↔
        ∃ γ : ℝ, ∃ σ : ℝ, 0 ≤ σ ∧
          ∃ ν : MeasureTheory.Measure ℝ,
            ν {0} = 0 ∧ (∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂ν < ∞) ∧
              ∀ t : ℝ, MeasureTheory.charFun μ t =
                Complex.exp ((Complex.I * (γ : ℂ) * (t : ℂ) -
                  (((σ ^ 2 * t ^ 2 : ℝ) : ℂ) / 2) +
                  ∫ x, (Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)) - 1 -
                    Set.indicator {y : ℝ | |y| ≤ 1}
                      (fun y => Complex.I * (t : ℂ) * (y : ℂ)) x) ∂ν))) := by
  intro mu hmu
  rw [Measure.isInfinitelyDivisible_iff_exists_iterate]
  constructor
  · intro hID
    obtain ⟨gamma, sigma, hsigma, nu, hnu0, hnu, hchar⟩ :=
      lk_triplet_of_infinitelyDivisible hID
    refine ⟨gamma, sigma, hsigma, nu, hnu0, hnu, fun t ↦ ?_⟩
    rw [hchar t]
    rfl
  · rintro ⟨gamma, sigma, -, nu, -, hnu, hchar⟩
    apply lk_infinitelyDivisible_of_charFun hmu hnu gamma sigma
    intro t
    rw [hchar t]
    rfl

end

end MetaMathlibExt
