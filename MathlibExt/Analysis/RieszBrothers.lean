/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`LeanEval/Analysis/RieszBrothers.lean` (leanprover/lean-eval,
https://github.com/leanprover/lean-eval), at commit 38361be884302c7edce1908c4aef8296eb2cb27e,
problem `riesz_brothers_theorem` (manifest `manifests/problems/riesz_brothers_theorem.toml`,
revision 1, submitter Yongxi Lin, status archived). The adaptation is the statement of
`riesz_brothers_theorem` and its accompanying text from
`WantedExt/Analysis/RieszBrothersWanted.lean`.
Copyright 2026 Lean FRO, LLC.
Authors: Yongxi Lin
Licensed under the Apache License, Version 2.0 (the "License");
you may not use these portions except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License. lean-eval ships no `NOTICE` file.

Modification notice (Apache License 2.0, Section 4). ATLAS moved the declaration to the
`MathlibExt.Analysis.RieszBrothersWanted.Analysis` namespace and initially converted it from
`@[eval_problem]` to `theorem_wanted`. ATLAS then supplied the proof and moved the declaration
to this module, preserving its full name, statement and docstring.
-/

module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.Normed.Operator.Mul
public import Mathlib.MeasureTheory.Measure.Complex
public import Mathlib.MeasureTheory.VectorMeasure.Integral

import Mathlib.Analysis.Complex.Poisson
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.VectorMeasure.SetIntegral
import Mathlib.MeasureTheory.VectorMeasure.Variation.SignedMeasure
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Riesz brothers' theorem

The Riesz brothers' theorem says that a complex Borel measure on the circle
whose positive analytic moments vanish is absolutely continuous with respect to
Haar measure.

The proof uses Herglotz integrals over small neighborhoods of compact Haar-null sets.
Subtracting the exponentials of their negatives from one gives uniformly bounded holomorphic
approximations to the indicators of those sets. Taylor expansion and dominated convergence then give
vanishing on compact Haar-null sets, and inner regularity gives absolute continuity.
-/

open MeasureTheory MeasureTheory.Measure Complex Metric Set Filter
open scoped ENNReal NNReal Topology

namespace MathlibExt.Analysis.RieszBrothersWanted.Analysis

private noncomputable def circlePoint (x : UnitAddCircle) : ℂ := fourier 1 x

private lemma continuous_circlePoint : Continuous circlePoint := (fourier 1).continuous

private lemma circlePoint_norm (x : UnitAddCircle) : ‖circlePoint x‖ = 1 :=
  Circle.norm_coe _

private lemma circlePoint_injective : Function.Injective circlePoint := by
  intro x y h
  refine AddCircle.injective_toCircle one_ne_zero (Subtype.ext ?_)
  simpa only [circlePoint, fourier_one] using h

private noncomputable def circleMeasure : Measure ℂ :=
  AddCircle.haarAddCircle.map circlePoint

private instance : IsProbabilityMeasure circleMeasure :=
  (Measure.isProbabilityMeasure_map_iff continuous_circlePoint.measurable.aemeasurable).2
    inferInstance

private lemma ae_circleMeasure_norm : ∀ᵐ z ∂circleMeasure, ‖z‖ = 1 :=
  (ae_map_iff continuous_circlePoint.measurable.aemeasurable (measurableSet_eq_fun
    continuous_norm.measurable measurable_const)).2 (ae_of_all _ circlePoint_norm)

private lemma circleMap_mul (x : ℝ) :
    circleMap (0 : ℂ) 1 (2 * Real.pi * x) = circlePoint x := by
  rw [circlePoint, fourier_coe_apply, circleMap]
  simp only [Int.cast_one, ofReal_one, mul_one, one_mul, div_one, ofReal_mul,
    ofReal_ofNat, zero_add]
  congr 1
  ring

private lemma average_eq_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {f : ℂ → E} (hf : AEStronglyMeasurable f circleMeasure) :
    Real.circleAverage f 0 1 = ∫ z, f z ∂circleMeasure := by
  rw [Real.circleAverage_def, circleMeasure,
    integral_map continuous_circlePoint.measurable.aemeasurable hf,
    AddCircle.integral_haarAddCircle]
  simp only [inv_one, one_smul]
  rw [← AddCircle.intervalIntegral_preimage (T := 1) 0]
  simp only [zero_add]
  simp_rw [← circleMap_mul]
  simpa using (intervalIntegral.integral_comp_mul_left (fun θ ↦ f (circleMap 0 1 θ))
    (mul_ne_zero two_ne_zero Real.pi_ne_zero) (a := 0) (b := 1)).symm

private lemma re_kernel (w z : ℂ) :
    (herglotzRieszKernel 0 w z).re = (‖z‖ ^ 2 - ‖w‖ ^ 2) / ‖z - w‖ ^ 2 := by
  rw [← Function.comp_apply (f := Complex.re), ← poissonKernel_eq_re_herglotzRieszKernel]
  simp [poissonKernel_def]

private lemma kernel_continuousOn {w : ℂ} (hw : ‖w‖ < 1) :
    ContinuousOn (herglotzRieszKernel 0 w) (sphere 0 1) := by
  simpa only [abs_one] using
    continuousOn_herglotzRieszKernel_sphere (c := 0) (R := 1) (by simpa using hw.ne)

private lemma kernel_integrable {w : ℂ} (hw : ‖w‖ < 1) :
    Integrable (herglotzRieszKernel 0 w) circleMeasure := by
  have h : IntegrableOn (herglotzRieszKernel 0 w) (sphere 0 1) circleMeasure :=
    (kernel_continuousOn hw).integrableOn_compact (isCompact_sphere _ _)
  have hfull : circleMeasure.restrict (sphere 0 1) = circleMeasure :=
    restrict_eq_self_of_ae_mem (by simpa [mem_sphere_zero_iff_norm] using ae_circleMeasure_norm)
  rwa [IntegrableOn, hfull] at h

private lemma average_re_kernel {w : ℂ} (hw : ‖w‖ < 1) :
    ∫ z, (herglotzRieszKernel 0 w z).re ∂circleMeasure = 1 := by
  have hk := (kernel_integrable hw).aestronglyMeasurable
  rw [← average_eq_integral (Complex.continuous_re.comp_aestronglyMeasurable hk)]
  have hconst : DiffContOnCl ℂ (fun _ : ℂ ↦ (1 : ℂ)) (ball 0 1) := diffContOnCl_const
  have h := hconst.circleAverage_re_herglotzRieszKernel_smul (mem_ball_zero_iff.mpr hw)
  have hint : CircleIntegrable ((Complex.re ∘ herglotzRieszKernel 0 w) •
      (fun _ ↦ (1 : ℂ))) 0 1 :=
    ((Complex.continuous_re.comp_continuousOn (kernel_continuousOn hw)).smul
      continuousOn_const).circleIntegrable zero_le_one
  have hre := congrArg Complex.reCLM h
  rw [← Complex.reCLM.circleAverage_comp_comm hint] at hre
  simpa [Function.comp_def, real_smul] using hre

private lemma complexVariation_finite {X : Type*} [MeasurableSpace X] (μ : ComplexMeasure X) :
    IsFiniteMeasure μ.variation := by
  have h : μ.variation ≤ μ.re.totalVariation + μ.im.totalVariation := by
    apply VectorMeasure.variation_le_of_forall_eNorm_le
    intro S hS
    rw [add_apply]
    calc
      ‖μ S‖ₑ = ENNReal.ofReal ‖μ S‖ := (ofReal_norm _).symm
      _ ≤ ENNReal.ofReal (|(μ S).re| + |(μ S).im|) :=
        ENNReal.ofReal_le_ofReal (Complex.norm_le_abs_re_add_abs_im _)
      _ = ‖μ.re S‖ₑ + ‖μ.im S‖ₑ := by
        rw [ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _), ← ofReal_norm, ← ofReal_norm]
        rfl
      _ ≤ μ.re.totalVariation S + μ.im.totalVariation S :=
        add_le_add (μ.re.eNorm_le_totalVariation S) (μ.im.eNorm_le_totalVariation S)
  exact ⟨(h univ).trans_lt (measure_lt_top _ _)⟩

private lemma circlePoint_pow (n : ℕ) (x : UnitAddCircle) :
    circlePoint x ^ n = fourier n x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, Nat.cast_succ, fourier_add, circlePoint]

private lemma vectorIntegral_const_mul {X : Type*} [MeasurableSpace X] (μ : ComplexMeasure X)
    (c : ℂ) (f : X → ℂ) :
    ∫ᵛ x, c * f x ∂[ContinuousLinearMap.mul ℝ ℂ; μ] =
      c * ∫ᵛ x, f x ∂[ContinuousLinearMap.mul ℝ ℂ; μ] := by
  simp only [← smul_eq_mul, ← Pi.smul_apply, VectorMeasure.integral_eq_setToFun]
  apply setToFun_smul
  intro a S z
  change (a * z) * μ S = a * (z * μ S)
  exact mul_assoc _ _ _

private lemma integral_eq_origin (μ : ComplexMeasure UnitAddCircle)
    (hμ : ∀ n : ℕ, 1 ≤ n →
      ∫ᵛ x, fourier n x ∂[ContinuousLinearMap.mul ℝ ℂ; μ] = 0)
    [IsFiniteMeasure μ.variation] {F : ℂ → ℂ} {R : ℝ≥0} (hR : 1 < R)
    (hF : DifferentiableOn ℂ F (closedBall 0 R)) :
    ∫ᵛ x, F (circlePoint x) ∂[ContinuousLinearMap.mul ℝ ℂ; μ] = F 0 * μ univ := by
  let p := cauchyPowerSeries F 0 R
  have hp : HasFPowerSeriesOnBall F p 0 R := hF.hasFPowerSeriesOnBall (zero_lt_one.trans hR)
  let a (n : ℕ) : ℂ := p n (fun _ ↦ 1)
  have hterm (n : ℕ) (z : ℂ) : p n (fun _ ↦ z) = z ^ n * a n := by
    simpa only [a, smul_eq_mul, mul_one, Finset.prod_const, Finset.card_fin] using
      (p n).map_smul_univ (fun _ ↦ z) (fun _ ↦ 1)
  have hsummable : Summable fun n ↦ ‖p n‖ := by
    have hrad : (↑(1 : ℝ≥0) : ℝ≥0∞) < (↑R : ℝ≥0∞) := ENNReal.coe_lt_coe.mpr hR
    simpa using p.summable_norm_mul_pow (hrad.trans_le hp.r_le)
  have hbound (n : ℕ) (x : UnitAddCircle) : ‖a n * fourier n x‖ ≤ ‖p n‖ := by
    rw [← circlePoint_pow, mul_comm, ← hterm]
    simpa only [circlePoint_norm, Finset.prod_const, one_pow, mul_one] using
      (p n).le_opNorm (fun _ ↦ circlePoint x)
  have hpoint (x : UnitAddCircle) : HasSum (fun n ↦ a n * fourier n x) (F (circlePoint x)) := by
    have hmem : circlePoint x ∈ eball (0 : ℂ) R := by
      rw [Metric.eball_coe, mem_ball_zero_iff, circlePoint_norm]
      exact_mod_cast hR
    simpa [hterm, circlePoint_pow, mul_comm] using hp.hasSum_sub hmem
  have hsum : HasSum (fun n : ℕ ↦
      ∫ᵛ x, a n * fourier n x ∂[ContinuousLinearMap.mul ℝ ℂ; μ])
      (∫ᵛ x, F (circlePoint x) ∂[ContinuousLinearMap.mul ℝ ℂ; μ]) :=
    VectorMeasure.hasSum_integral_of_dominated_convergence
    (B := ContinuousLinearMap.mul ℝ ℂ) (μ := μ)
    (fun n _ ↦ ‖p n‖)
    (fun n ↦ (continuous_const.mul (fourier n).continuous).aestronglyMeasurable)
    (fun n ↦ ae_of_all _ (hbound n)) (ae_of_all _ (fun _ ↦ hsummable)) (integrable_const _)
    (ae_of_all _ hpoint)
  rw [← hsum.tsum_eq, tsum_eq_single 0]
  · simp only [Nat.cast_zero, fourier_zero, mul_one, VectorMeasure.integral_const,
      ContinuousLinearMap.mul_apply', show a 0 = F 0 from hp.coeff_zero _]
  · intro n hn
    rw [vectorIntegral_const_mul, hμ n (Nat.pos_of_ne_zero hn), mul_zero]

private noncomputable def herglotzIntegral (U : Set ℂ) (w : ℂ) : ℂ :=
  ∫ z in U, herglotzRieszKernel 0 w z ∂circleMeasure

private lemma re_herglotzIntegral {U : Set ℂ} {w : ℂ} (hw : ‖w‖ < 1) :
    (herglotzIntegral U w).re = ∫ z in U, (herglotzRieszKernel 0 w z).re ∂circleMeasure :=
  (Complex.reCLM.integral_comp_comm (kernel_integrable hw).integrableOn).symm

private lemma re_herglotzIntegral_nonneg (U : Set ℂ) {w : ℂ} (hw : ‖w‖ < 1) :
    0 ≤ (herglotzIntegral U w).re := by
  rw [re_herglotzIntegral hw]
  apply integral_nonneg_of_ae
  filter_upwards [ae_mono restrict_le_self ae_circleMeasure_norm] with z hz
  rw [re_kernel, hz]
  exact div_nonneg (by nlinarith [norm_nonneg w]) (sq_nonneg _)

private lemma herglotzIntegral_zero (U : Set ℂ) :
    herglotzIntegral U 0 = (circleMeasure.real U : ℂ) := by
  calc
    herglotzIntegral U 0 = ∫ _ in U, (1 : ℂ) ∂circleMeasure := by
      apply integral_congr_ae
      filter_upwards [ae_mono restrict_le_self ae_circleMeasure_norm] with z hz
      have hz' : z ≠ 0 := fun h ↦ by simp [h] at hz
      simp [herglotzRieszKernel_def, hz']
    _ = (circleMeasure.real U : ℂ) := by simp [real_smul]

private lemma differentiableOn_herglotzIntegral {U : Set ℂ} (hU : MeasurableSet U) :
    DifferentiableOn ℂ (herglotzIntegral U) (ball 0 1) := by
  let g := U.indicator (fun _ : ℂ ↦ (1 : ℂ))
  have hg : CircleIntegrable g 0 1 := by
    rw [CircleIntegrable, intervalIntegrable_iff, uIoc_of_le Real.two_pi_pos.le]
    change Integrable (fun θ ↦ U.indicator (fun _ : ℂ ↦ (1 : ℂ)) (circleMap 0 1 θ)) _
    simp only [← indicator_comp_right]
    exact (integrable_const (1 : ℂ)).indicator
      (hU.preimage (continuous_circleMap 0 1).measurable)
  have hdiff := differentiableOn_circleAverage_herglotzRieszKernel_smul hg
  have hsub : ball (0 : ℂ) 1 ⊆ (sphere (0 : ℂ) |(1 : ℝ)|)ᶜ := by
    intro w hw
    simpa [mem_sphere_zero_iff_norm] using (mem_ball_zero_iff.mp hw).ne
  apply (hdiff.mono hsub).congr
  intro w hw
  have hw' := mem_ball_zero_iff.mp hw
  rw [herglotzIntegral, ← integral_indicator hU]
  have hfun : (fun z ↦ herglotzRieszKernel 0 w z • g z) =
      U.indicator (herglotzRieszKernel 0 w) := by
    funext z
    by_cases hz : z ∈ U <;> simp [g, hz, smul_eq_mul]
  rw [hfun, average_eq_integral]
  exact ((kernel_integrable hw').indicator hU).aestronglyMeasurable

private lemma norm_herglotzIntegral_le {U : Set ℂ} (hU : MeasurableSet U) {w : ℂ} (hw : ‖w‖ < 1)
    {d : ℝ} (hd : 0 < d) (hsep : ∀ z ∈ U, d ≤ ‖z - w‖) :
    ‖herglotzIntegral U w‖ ≤ (2 / d) * circleMeasure.real U := by
  rw [herglotzIntegral, ← measureReal_restrict_apply_univ]
  apply norm_integral_le_of_norm_le_const
  filter_upwards [ae_mono restrict_le_self ae_circleMeasure_norm, ae_restrict_mem hU] with z hz hzU
  rw [herglotzRieszKernel_def, sub_zero, norm_div, sub_zero]
  calc
    ‖z + w‖ / ‖z - w‖ ≤ (‖z‖ + ‖w‖) / ‖z - w‖ :=
      div_le_div_of_nonneg_right (norm_add_le _ _) (norm_nonneg _)
    _ ≤ 2 / d := by
      have hzw := hsep z hzU
      have hn : ‖z‖ + ‖w‖ ≤ 2 := by linarith
      gcongr

private lemma half_le_re_herglotzIntegral {U : Set ℂ} (hU : MeasurableSet U) {w : ℂ}
    (hw : ‖w‖ < 1) {d : ℝ} (hd : 0 < d) (hsep : ∀ z ∉ U, d ≤ ‖z - w‖)
    (hsmall : 1 - ‖w‖ ^ 2 ≤ d ^ 2 / 2) :
    1 / 2 ≤ (herglotzIntegral U w).re := by
  have hk : Integrable (fun z ↦ (herglotzRieszKernel 0 w z).re) circleMeasure :=
    Complex.reCLM.integrable_comp (kernel_integrable hw)
  have htotal := (integral_add_compl hU hk).trans (average_re_kernel hw)
  have hcompl : (∫ z in Uᶜ, (herglotzRieszKernel 0 w z).re ∂circleMeasure) ≤ 1 / 2 := by
    have hle : ∀ᵐ z ∂circleMeasure.restrict Uᶜ, (herglotzRieszKernel 0 w z).re ≤ 1 / 2 := by
      filter_upwards [ae_mono restrict_le_self ae_circleMeasure_norm, ae_restrict_mem hU.compl]
        with z hz hzU
      have hzw := hsep z hzU
      rw [re_kernel, hz, one_pow, div_le_iff₀ (sq_pos_of_pos (hd.trans_le hzw))]
      have : d ^ 2 ≤ ‖z - w‖ ^ 2 := by gcongr
      linarith
    calc
      _ ≤ ∫ _ in Uᶜ, (1 / 2 : ℝ) ∂circleMeasure :=
        integral_mono_ae hk.integrableOn (integrable_const _) hle
      _ ≤ 1 / 2 := by
        have hmass : circleMeasure.real Uᶜ ≤ 1 := by
          rw [← probReal_univ (μ := circleMeasure)]
          exact measureReal_mono (subset_univ _)
        rw [setIntegral_const, smul_eq_mul]
        calc
          _ ≤ 1 * (1 / 2 : ℝ) := mul_le_mul_of_nonneg_right hmass (by norm_num)
          _ = _ := one_mul _
  rw [re_herglotzIntegral hw]
  linarith

private lemma norm_sub_scaled {z : ℂ} (hz : ‖z‖ = 1) {r : ℝ} (hr : r ≤ 1) :
    ‖z - (r : ℂ) * z‖ = 1 - r := by
  rw [show z - (r : ℂ) * z = ((1 - r : ℝ) : ℂ) * z by push_cast; ring,
    norm_mul, hz, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hr)]

private lemma norm_scaled {z : ℂ} (hz : ‖z‖ = 1) {r : ℝ} (hr : 0 ≤ r) :
    ‖(r : ℂ) * z‖ = r := by
  rw [norm_mul, hz, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]

/-- Choose a neighborhood of small measure and then a radius whose Poisson mass there
is at least one half at each point of the compact set. -/
private lemma exists_herglotz_data {K : Set ℂ} (hK : IsCompact K) (hnull : circleMeasure K = 0)
    (hnorm : ∀ z ∈ K, ‖z‖ = 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ U, IsOpen U ∧ U ⊆ thickening ε K ∧ circleMeasure.real U ≤ ε ^ 2 ∧
      ∃ r : ℝ, 0 < r ∧ r < 1 ∧ 1 - r ≤ ε ∧
        ∀ z ∈ K, 1 / 2 ≤ (herglotzIntegral U ((r : ℂ) * z)).re := by
  obtain ⟨V, hKV, hV, hmass⟩ := K.exists_isOpen_lt_of_lt (μ := circleMeasure)
    (ENNReal.ofReal (ε ^ 2)) (by rw [hnull]; positivity)
  let U := V ∩ thickening ε K
  have hU : IsOpen U := hV.inter isOpen_thickening
  have hKU : K ⊆ U := subset_inter hKV (self_subset_thickening hε K)
  obtain ⟨d, hd, hKU'⟩ := hK.exists_thickening_subset_open hU hKU
  let t := min ε (min (d / 2) (min (d ^ 2 / 16) (1 / 2)))
  have ht : 0 < t := by dsimp [t]; positivity
  have htε : t ≤ ε := min_le_left _ _
  have htd : t ≤ d / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have htd2 : t ≤ d ^ 2 / 16 :=
    (min_le_right _ _).trans <| (min_le_right _ _).trans (min_le_left _ _)
  have ht1 : t ≤ 1 / 2 :=
    (min_le_right _ _).trans <| (min_le_right _ _).trans (min_le_right _ _)
  let r := 1 - t
  have hr : 0 < r := by dsimp [r]; linarith
  have hr1 : r < 1 := by dsimp [r]; linarith
  refine ⟨U, hU, inter_subset_right, ?_, r, hr, hr1, by dsimp [r]; linarith, ?_⟩
  · refine (measureReal_mono (μ := circleMeasure) (inter_subset_left : U ⊆ V)).trans ?_
    exact ENNReal.toReal_le_of_le_ofReal (sq_nonneg _) hmass.le
  · intro z hz
    have hw := norm_scaled (hnorm z hz) hr.le
    refine half_le_re_herglotzIntegral hU.measurableSet (hw.trans_lt hr1)
      (half_pos hd) ?_ ?_
    · intro y hy
      have hdist : d ≤ ‖y - z‖ := by
        by_contra! hlt
        exact hy (hKU' (Metric.mem_thickening_iff.mpr ⟨z, hz, by rwa [dist_eq_norm]⟩))
      have htri := dist_triangle y ((r : ℂ) * z) z
      rw [dist_eq_norm, dist_eq_norm, dist_comm ((r : ℂ) * z) z, dist_eq_norm,
        norm_sub_scaled (hnorm z hz) hr1.le] at htri
      dsimp [r] at htri
      linarith
    · rw [hw]
      dsimp [r]
      nlinarith [sq_nonneg t]

private lemma exists_indicator_approximation {K : Set ℂ} (hK : IsCompact K)
    (hKne : K.Nonempty) (hnull : circleMeasure K = 0) (hnorm : ∀ z ∈ K, ‖z‖ = 1) :
    ∃ (F : ℕ → ℂ → ℂ) (R : ℕ → ℝ≥0),
      (∀ n, 1 < R n ∧ DifferentiableOn ℂ (F n) (closedBall 0 (R n))) ∧
      (∀ n z, ‖z‖ = 1 → ‖F n z‖ ≤ 2) ∧
      (∀ z, ‖z‖ = 1 → Tendsto (fun n ↦ F n z) atTop (𝓝 (K.indicator (fun _ ↦ 1) z))) ∧
      Tendsto (fun n ↦ F n 0) atTop (𝓝 0) := by
  classical
  let ε (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  choose U hU hUsmall hmass r hr hr1 hrnear hpeak using
    fun n : ℕ ↦ exists_herglotz_data hK hnull hnorm (hε n)
  let H (n : ℕ) (z : ℂ) := herglotzIntegral (U n) ((r n : ℂ) * z) / (ε n : ℂ)
  let F (n : ℕ) (z : ℂ) := 1 - Complex.exp (-H n z)
  have hunit (n : ℕ) {z : ℂ} (hz : ‖z‖ = 1) : ‖(r n : ℂ) * z‖ < 1 :=
    (norm_scaled hz (hr n).le).trans_lt (hr1 n)
  have hre (n : ℕ) (z : ℂ) : (H n z).re =
      (herglotzIntegral (U n) ((r n : ℂ) * z)).re / ε n := Complex.div_ofReal_re _ _
  have hfromzero {z : ℂ} (hz : Tendsto (fun n ↦ H n z) atTop (𝓝 0)) :
      Tendsto (fun n ↦ F n z) atTop (𝓝 0) := by
    have hc : Continuous (fun w : ℂ ↦ 1 - Complex.exp (-w)) := by fun_prop
    have ht := (hc.tendsto 0).comp hz
    change Tendsto (fun n ↦ F n z) atTop (𝓝 (1 - Complex.exp (-(0 : ℂ)))) at ht
    simpa only [neg_zero, Complex.exp_zero, sub_self] using ht
  have hHbound {n : ℕ} {z : ℂ} {c : ℝ} (hc : 0 ≤ c)
      (h : ‖herglotzIntegral (U n) ((r n : ℂ) * z)‖ ≤ c * circleMeasure.real (U n)) :
      ‖H n z‖ ≤ c * ε n := by
    change ‖herglotzIntegral (U n) ((r n : ℂ) * z) / (ε n : ℂ)‖ ≤ _
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hε n)]
    apply (div_le_iff₀ (hε n)).2
    calc
      _ ≤ c * circleMeasure.real (U n) := h
      _ ≤ c * ε n ^ 2 := mul_le_mul_of_nonneg_left (hmass n) hc
      _ = _ := by ring
  have hFdiff (n : ℕ) : ∃ R : ℝ≥0, 1 < R ∧ DifferentiableOn ℂ (F n) (closedBall 0 R) := by
    obtain ⟨R, hR1, hR⟩ := exists_between (show (1 : ℝ) < (r n)⁻¹ from
      (one_lt_inv₀ (hr n)).mpr (hr1 n))
    let R' : ℝ≥0 := ⟨R, zero_le_one.trans hR1.le⟩
    refine ⟨R', hR1, ?_⟩
    have hmap : MapsTo (fun z : ℂ ↦ (r n : ℂ) * z) (closedBall 0 R) (ball 0 1) := by
      intro z hz
      have hz' := mem_closedBall_zero_iff.mp hz
      rw [mem_ball_zero_iff, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hr n)]
      exact (mul_le_mul_of_nonneg_left hz' (hr n).le).trans_lt
        (by
          rw [← one_div] at hR
          simpa only [mul_comm] using (lt_div_iff₀ (hr n)).mp hR)
    have hH : DifferentiableOn ℂ (H n) (closedBall 0 R) :=
      ((differentiableOn_herglotzIntegral (hU n).measurableSet).comp
        (by fun_prop) hmap).div_const _
    exact (differentiableOn_const (1 : ℂ)).sub hH.neg.cexp
  choose R hR hdiff using hFdiff
  refine ⟨F, R, fun n ↦ ⟨hR n, hdiff n⟩, ?_, ?_, ?_⟩
  · intro n z hz
    have hnr : 0 ≤ (H n z).re := by
      rw [hre]
      exact div_nonneg (re_herglotzIntegral_nonneg _ (hunit n hz)) (hε n).le
    calc
      ‖F n z‖ ≤ 1 + ‖Complex.exp (-H n z)‖ := by
        simpa only [F, norm_one] using norm_sub_le (1 : ℂ) (Complex.exp (-H n z))
      _ ≤ 2 := by
        rw [Complex.norm_exp, Complex.neg_re]
        have hExp : Real.exp (-(H n z).re) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hnr)
        linarith
  · intro z hz
    by_cases hzK : z ∈ K
    · rw [indicator_of_mem hzK]
      have hexp : Tendsto (fun n ↦ Complex.exp (-H n z)) atTop (𝓝 0) := by
        apply squeeze_zero_norm (a := fun n : ℕ ↦ Real.exp (-(((n : ℝ) + 1) / 2)))
        · intro n
          rw [Complex.norm_exp, Complex.neg_re, Real.exp_le_exp, neg_le_neg_iff, hre,
            le_div_iff₀ (hε n)]
          have hn : (n : ℝ) + 1 ≠ 0 := by positivity
          convert hpeak n z hzK using 1
          dsimp [ε]
          field_simp
        · apply Real.tendsto_exp_atBot.comp
          exact tendsto_neg_atTop_atBot.comp
            ((tendsto_atTop_add_const_right atTop 1
              (tendsto_natCast_atTop_atTop (R := ℝ))).atTop_div_const (r := 2) (by norm_num))
      simpa only [F, sub_zero] using (tendsto_const_nhds (x := (1 : ℂ))).sub hexp
    · rw [indicator_of_notMem hzK]
      apply hfromzero
      let d := infDist z K
      have hd : 0 < d := (hK.isClosed.notMem_iff_infDist_pos hKne).mp hzK
      apply squeeze_zero_norm' (a := fun n ↦ (2 / (d / 2)) * ε n)
      · filter_upwards [hεlim.eventually (gt_mem_nhds (show 0 < d / 4 by positivity))]
          with n hn
        refine hHbound (by positivity) (norm_herglotzIntegral_le (hU n).measurableSet
          (hunit n hz) (half_pos hd) ?_)
        intro y hy
        obtain ⟨k, hk, hyk⟩ := Metric.mem_thickening_iff.mp (hUsmall n hy)
        have htri := (infDist_le_dist_of_mem hk).trans (dist_triangle4 z ((r n : ℂ) * z) y k)
        rw [dist_eq_norm z ((r n : ℂ) * z), norm_sub_scaled hz (hr1 n).le,
          dist_comm ((r n : ℂ) * z) y, dist_eq_norm y ((r n : ℂ) * z)] at htri
        have hnear := hrnear n
        change ε n < d / 4 at hn
        change d ≤ _ at htri
        linarith
      · simpa only [mul_zero] using hεlim.const_mul (2 / (d / 2))
  · apply hfromzero
    apply squeeze_zero_norm (a := ε)
    · intro n
      simpa only [one_mul] using hHbound (c := 1) zero_le_one (z := 0) (by
        rw [mul_zero, herglotzIntegral_zero, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg measureReal_nonneg, one_mul])
    · exact hεlim

private lemma measure_compact_null (μ : ComplexMeasure UnitAddCircle)
    (hμ : ∀ n : ℕ, 1 ≤ n → ∫ᵛ z, fourier n z ∂[ContinuousLinearMap.mul ℝ ℂ; μ] = 0)
    [IsFiniteMeasure μ.variation] {K : Set UnitAddCircle} (hK : IsCompact K)
    (hnull : AddCircle.haarAddCircle K = 0) : μ K = 0 := by
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · exact μ.empty
  let L := circlePoint '' K
  have hL : IsCompact L := hK.image continuous_circlePoint
  have hLnull : circleMeasure L = 0 := by
    rw [circleMeasure,
      Measure.map_apply continuous_circlePoint.measurable hL.isClosed.measurableSet]
    simpa [L, Set.preimage_image_eq _ circlePoint_injective] using hnull
  have hLnorm : ∀ z ∈ L, ‖z‖ = 1 := by
    rintro _ ⟨x, _, rfl⟩
    exact circlePoint_norm x
  obtain ⟨F, R, hdiff, hbound, hpoint, h0⟩ :=
    exists_indicator_approximation hL (hKne.image circlePoint) hLnull hLnorm
  have hlim : Tendsto (fun n ↦ ∫ᵛ x, F n (circlePoint x) ∂[ContinuousLinearMap.mul ℝ ℂ; μ])
      atTop (𝓝 (μ K)) := by
    have hlim' := VectorMeasure.tendsto_integral_of_dominated_convergence
      (B := ContinuousLinearMap.mul ℝ ℂ) (μ := μ) (fun _ ↦ 2)
      (fun n ↦ ?_) (integrable_const _) (fun n ↦ ae_of_all _
        (fun x ↦ hbound n (circlePoint x) (circlePoint_norm x)))
      (ae_of_all _ (fun x ↦ hpoint (circlePoint x) (circlePoint_norm x)))
    · have hind (x : UnitAddCircle) : L.indicator (fun _ ↦ 1) (circlePoint x) =
          K.indicator (fun _ ↦ (1 : ℂ)) x := by
        have hmem : circlePoint x ∈ L ↔ x ∈ K := by
          change x ∈ circlePoint ⁻¹' L ↔ _
          rw [Set.preimage_image_eq _ circlePoint_injective]
        by_cases hx : x ∈ K
        · simp [hx, hmem.mpr hx]
        · simp [hx, mt hmem.mp hx]
      simpa only [hind, VectorMeasure.integral_indicator_const _ hK.isClosed.measurableSet,
        ContinuousLinearMap.mul_apply', one_mul] using hlim'
    · have hmaps : MapsTo circlePoint univ (closedBall 0 (R n)) := by
        intro x _
        rw [mem_closedBall_zero_iff, circlePoint_norm]
        exact_mod_cast (hdiff n).1.le
      exact (continuousOn_univ.1 ((hdiff n).2.continuousOn.comp
        continuous_circlePoint.continuousOn hmaps)).aestronglyMeasurable
  have hzero : Tendsto (fun n ↦ ∫ᵛ x, F n (circlePoint x) ∂[ContinuousLinearMap.mul ℝ ℂ; μ])
      atTop (𝓝 0) := by
    simpa only [← fun n ↦ integral_eq_origin μ hμ (hdiff n).1 (hdiff n).2, zero_mul] using
      h0.mul tendsto_const_nhds (b := μ univ)
  exact tendsto_nhds_unique hlim hzero

set_option linter.dupNamespace false in
/- **Riesz brothers' theorem.** Let `μ` be a complex Borel measure on
the unit circle such that `∫ z^n dμ = 0` for every `n ≥ 1`. Then `μ` is
absolutely continuous with respect to Haar measure. The usual density
formulation follows by applying the Radon–Nikodym theorem to this conclusion;
the hypothesis transfers the Fourier-vanishing property to that density. This
corollary is not part of the formal statement here. -/
/-- **F. and M. Riesz theorem.** Let $\mu$ be a complex Borel measure on the circle
$\mathbb{T} = \mathbb{R}/\mathbb{Z}$. If $\int_{\mathbb{T}} e^{2\pi i n z} \, d\mu(z) = 0$ for
every integer $n \ge 1$, then $\mu$ is absolutely continuous with respect to the Haar probability
measure on $\mathbb{T}$.

Source: W. Rudin, Real and Complex Analysis; N. K. Nikolski, Operators, Functions, and Systems:
An Easy Reading, Volume I: Hardy, Hankel, and Toeplitz. Via leanprover/lean-eval@38361be, problem
`riesz_brothers_theorem`. -/
public theorem riesz_brothers_theorem (μ : ComplexMeasure UnitAddCircle)
    (hμ : ∀ n : ℕ, 1 ≤ n → ∫ᵛ z, fourier n z ∂[ContinuousLinearMap.mul ℝ ℂ; μ] = 0) :
    μ ≪ᵥ AddCircle.haarAddCircle.toENNRealVectorMeasure := by
  let := complexVariation_finite μ
  intro S hSnull
  by_cases hS : MeasurableSet S
  · rw [Measure.toENNRealVectorMeasure_apply_measurable hS] at hSnull
    suffices ‖μ S‖ ≤ 0 from norm_eq_zero.mp (le_antisymm this (norm_nonneg _))
    refine le_of_forall_pos_le_add fun ε hε ↦ ?_
    obtain ⟨K, hKS, hK, hKvar⟩ := hS.exists_isCompact_sdiff_lt (μ := μ.variation)
      (measure_ne_top _ _) (ENNReal.ofReal_pos.mpr hε).ne'
    have hKnull : AddCircle.haarAddCircle K = 0 := measure_mono_null hKS hSnull
    have hμK : μ K = 0 := measure_compact_null μ hμ hK hKnull
    rw [zero_add, ← VectorMeasure.of_add_of_sdiff hK.isClosed.measurableSet hS hKS,
      hμK, zero_add]
    exact (VectorMeasure.norm_measure_le_variation (μ := μ) (measure_ne_top _ _)).trans
      (ENNReal.toReal_le_of_le_ofReal hε.le hKvar.le)
  · exact μ.not_measurable hS

end MathlibExt.Analysis.RieszBrothersWanted.Analysis
