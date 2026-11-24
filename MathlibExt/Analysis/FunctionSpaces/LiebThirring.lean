/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The Lieb–Thirring kinetic energy inequality

We prove the Lieb–Thirring kinetic energy inequality for finite orthonormal families of
smooth compactly supported complex functions on Euclidean space. The proof uses the frequency
decomposition in Frank's survey (arXiv:2007.09326v1), with a smooth cutoff and Bessel's inequality.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set SchwartzMap FourierTransform
open scoped ContDiff FourierTransform SchwartzMap LineDeriv ComplexInnerProductSpace

namespace MathlibExt.Analysis.FunctionSpaces.LiebThirringWanted

private abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)

private def bump : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩

private def cutoff {d : ℕ} (t : ℝ) (ξ : Space d) : ℝ :=
  if 0 < t then bump (2 * ‖ξ‖ ^ 2 / t) else 0

private theorem cutoff_nonneg {d : ℕ} (t : ℝ) (ξ : Space d) : 0 ≤ cutoff t ξ := by
  unfold cutoff
  split
  · exact bump.nonneg
  · exact le_rfl

private theorem cutoff_le_one {d : ℕ} (t : ℝ) (ξ : Space d) : cutoff t ξ ≤ 1 := by
  unfold cutoff
  split
  · exact bump.le_one
  · exact zero_le_one

private theorem cutoff_one {d : ℕ} {t : ℝ} (ht : 0 < t) {ξ : Space d}
    (hξ : 2 * ‖ξ‖ ^ 2 ≤ t) : cutoff t ξ = 1 := by
  rw [cutoff, ite_eq_left ht]
  apply bump.one_of_mem_closedBall
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_of_nonneg (by positivity)]
  exact (div_le_iff₀ ht).2 (by simpa [bump] using hξ)

private theorem cutoff_zero {d : ℕ} {t : ℝ} {ξ : Space d}
    (hξ : t ≤ ‖ξ‖ ^ 2) : cutoff t ξ = 0 := by
  by_cases ht : 0 < t
  · rw [cutoff, ite_eq_left ht]
    apply bump.zero_of_le_dist
    rw [dist_zero_right, Real.norm_of_nonneg (by positivity)]
    exact (le_div_iff₀ ht).2 (by dsimp [bump]; linarith)
  · simp [cutoff, ht]

private theorem cutoff_contDiff {d : ℕ} (t : ℝ) :
    ContDiff ℝ ∞ (cutoff (d := d) t) := by
  change ContDiff ℝ ∞ (fun ξ : Space d => if 0 < t then bump (2 * ‖ξ‖ ^ 2 / t) else 0)
  by_cases ht : 0 < t
  · simp only [ite_eq_left ht]
    exact bump.contDiff.comp ((contDiff_const.mul (contDiff_norm_sq ℝ)).div_const t)
  · simp only [ite_eq_right ht]
    exact contDiff_const

private theorem cutoff_measurable {d : ℕ} : Measurable (fun p : ℝ × Space d => cutoff p.1 p.2) :=
  (bump.continuous.measurable.comp
    ((measurable_const.mul (continuous_snd.norm.pow 2).measurable).div measurable_fst)).ite
      (measurableSet_lt measurable_const measurable_fst) measurable_const

private theorem cutoff_support {d : ℕ} (t : ℝ) :
    Function.support (cutoff (d := d) t) ⊆ Metric.ball 0 (Real.sqrt t) := by
  intro ξ hξ
  rw [Metric.mem_ball, dist_zero_right, Real.lt_sqrt (norm_nonneg _)]
  exact lt_of_not_ge (fun h => hξ (cutoff_zero h))

private theorem cutoff_compact {d : ℕ} (t : ℝ) :
    HasCompactSupport (cutoff (d := d) t) :=
  HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall 0 (Real.sqrt t))
    ((cutoff_support t).trans Metric.ball_subset_closedBall)

private def lowFrequency {d : ℕ} (t : ℝ) (f : 𝓢(Space d, ℂ)) : 𝓢(Space d, ℂ) :=
  ((cutoff_compact t).comp_left Complex.ofReal_zero |>.mul_right).toSchwartzMap
    ((Complex.ofRealCLM.contDiff.comp (cutoff_contDiff t)).mul (f.smooth ⊤))

private theorem lowFrequency_apply {d : ℕ} (t : ℝ) (f : 𝓢(Space d, ℂ)) (ξ : Space d) :
    lowFrequency t f ξ = (cutoff t ξ : ℂ) * f ξ := rfl

private def low {d : ℕ} (t : ℝ) (f : 𝓢(Space d, ℂ)) (x : Space d) : ℂ :=
  𝓕⁻ (lowFrequency t (𝓕 f)) x

private def high {d : ℕ} (t : ℝ) (f : 𝓢(Space d, ℂ)) (x : Space d) : ℂ :=
  f x - low t f x

private def phase {d : ℕ} (x ξ : Space d) : ℂ := (𝐞 (inner ℝ ξ x) : ℂ)

private theorem low_integral {d : ℕ} (t : ℝ) (f : 𝓢(Space d, ℂ)) (x : Space d) :
    low t f x = ∫ ξ, phase x ξ * ((cutoff t ξ : ℂ) * 𝓕 f ξ) := by
  simp [low, fourierInv_coe, Real.fourierInv_eq, Circle.smul_def, phase, lowFrequency_apply]

private theorem phase_norm {d : ℕ} (x ξ : Space d) : ‖phase x ξ‖ = 1 := Circle.norm_coe _

private theorem phase_continuous {d : ℕ} :
    Continuous (fun p : Space d × Space d => phase p.1 p.2) :=
  continuous_subtype_val.comp (Real.continuous_fourierChar.comp
    (continuous_snd.inner continuous_fst))

private theorem high_measurable {d : ℕ} (f : 𝓢(Space d, ℂ)) :
    Measurable (fun p : Space d × ℝ => high p.2 f p.1) := by
  simp_rw [high, low_integral]
  apply (f.continuous.measurable.comp measurable_fst).sub
  apply StronglyMeasurable.measurable
  apply StronglyMeasurable.integral_prod_right
  apply Measurable.stronglyMeasurable
  exact (phase_continuous.measurable.comp
    (measurable_fst.fst.prodMk measurable_snd)).mul
    ((Complex.continuous_ofReal.measurable.comp
      (cutoff_measurable.comp (measurable_fst.snd.prodMk measurable_snd))).mul
      ((𝓕 f).continuous.measurable.comp measurable_snd))

private theorem inner_toLp {d : ℕ} {f g : Space d → ℂ}
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    ⟪hf.toLp f, hg.toLp g⟫ = ∫ ξ, star (f ξ) * g ξ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with ξ h₁ h₂
  rw [h₁, h₂]
  exact mul_comm _ _

private theorem norm_toLp_sq {d : ℕ} {g : Space d → ℂ} (hg : MemLp g 2 volume)
    (hgcont : Continuous g) (hgcs : HasCompactSupport g) :
    ‖hg.toLp g‖ ^ 2 = ∫ ξ, ‖g ξ‖ ^ 2 := by
  have hprod : Integrable (fun ξ => star (g ξ) * g ξ) :=
    ((continuous_star.comp hgcont).mul hgcont).integrable_of_hasCompactSupport hgcs.mul_left
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), inner_toLp, ← integral_re hprod]
  apply integral_congr_ae
  apply ae_of_all
  intro ξ
  change RCLike.re (star (g ξ) * g ξ) = ‖g ξ‖ ^ 2
  rw [show star (g ξ) * g ξ = ⟪g ξ, g ξ⟫ from mul_comm _ _]
  exact (norm_sq_eq_re_inner (𝕜 := ℂ) _).symm

private theorem cutoff_sq_integral_le {d : ℕ} (t : ℝ) :
    (∫ ξ : Space d, cutoff t ξ ^ 2) ≤ volume.real (Metric.ball (0 : Space d) (Real.sqrt t)) := by
  let s := Metric.ball (0 : Space d) (Real.sqrt t)
  have hsInt : Integrable (s.indicator (fun _ => (1 : ℝ))) :=
    (integrable_indicator_iff measurableSet_ball).2
      (integrableOn_const measure_ball_lt_top.ne)
  have hcs : HasCompactSupport (fun ξ : Space d => cutoff t ξ ^ 2) := by
    simpa only [Real.rpow_two] using
      (cutoff_compact (d := d) t).rpow_const (by norm_num : (2 : ℝ) ≠ 0)
  have hInt : Integrable (fun ξ : Space d => cutoff t ξ ^ 2) :=
    ((cutoff_contDiff t).continuous.pow 2).integrable_of_hasCompactSupport hcs
  calc
    _ ≤ ∫ ξ, s.indicator (fun _ => (1 : ℝ)) ξ := by
      apply integral_mono hInt hsInt
      intro ξ
      change cutoff t ξ ^ 2 ≤ s.indicator (fun _ => (1 : ℝ)) ξ
      by_cases hξ : ξ ∈ s
      · rw [indicator_of_mem hξ]
        simpa only [one_pow] using
          (sq_le_sq₀ (cutoff_nonneg t ξ) zero_le_one).2 (cutoff_le_one t ξ)
      · have hzero : cutoff t ξ = 0 :=
          Function.notMem_support.mp (fun h => hξ (cutoff_support t h))
        rw [indicator_of_notMem hξ, hzero]
        norm_num
    _ = _ := by rw [integral_indicator measurableSet_ball]; simp

private def cutoffKernel {d : ℕ} (t : ℝ) (x ξ : Space d) : ℂ :=
  star (phase x ξ) * (cutoff t ξ : ℂ)

private theorem cutoffKernel_continuous {d : ℕ} (t : ℝ) (x : Space d) :
    Continuous (cutoffKernel t x) :=
  (continuous_star.comp (phase_continuous.comp (continuous_const.prodMk continuous_id))).mul
    (Complex.continuous_ofReal.comp (cutoff_contDiff t).continuous)

private theorem cutoffKernel_compact {d : ℕ} (t : ℝ) (x : Space d) :
    HasCompactSupport (cutoffKernel t x) :=
  (cutoff_compact t).comp_left Complex.ofReal_zero |>.mul_left

private theorem cutoffKernel_memLp {d : ℕ} (t : ℝ) (x : Space d) :
    MemLp (cutoffKernel t x) 2 volume :=
  (cutoffKernel_continuous t x).memLp_of_hasCompactSupport (cutoffKernel_compact t x)

private def cutoffKernelLp {d : ℕ} (t : ℝ) (x : Space d) : Space d →₂[volume] ℂ :=
  (cutoffKernel_memLp t x).toLp (cutoffKernel t x)

private theorem low_eq_inner {d : ℕ} (t : ℝ) (f : 𝓢(Space d, ℂ)) (x : Space d) :
    low t f x = ⟪cutoffKernelLp t x, (𝓕 f).toLp 2 volume⟫ := by
  calc
    _ = ∫ ξ, phase x ξ * ((cutoff t ξ : ℂ) * 𝓕 f ξ) := low_integral t f x
    _ = ∫ ξ, star (cutoffKernel t x ξ) * 𝓕 f ξ := by
      apply integral_congr_ae
      exact ae_of_all _ fun ξ => by simp [cutoffKernel, mul_left_comm, mul_comm, mul_assoc]
    _ = _ := (inner_toLp (cutoffKernel_memLp t x) ((𝓕 f).memLp 2 volume)).symm

private theorem low_norm_eq_inner_norm {d : ℕ} (t : ℝ) (f : 𝓢(Space d, ℂ))
    (x : Space d) : ‖low t f x‖ = ‖⟪(𝓕 f).toLp 2 volume, cutoffKernelLp t x⟫‖ := by
  calc
    _ = ‖⟪cutoffKernelLp t x, (𝓕 f).toLp 2 volume⟫‖ :=
      congrArg (fun z : ℂ => ‖z‖) (low_eq_inner t f x)
    _ = _ := norm_inner_symm (𝕜 := ℂ) (cutoffKernelLp t x) ((𝓕 f).toLp 2 volume)

private theorem cutoffKernelLp_norm_le {d : ℕ} (t : ℝ) (x : Space d) :
    ‖cutoffKernelLp t x‖ ^ 2 ≤ volume.real (Metric.ball (0 : Space d) (Real.sqrt t)) := by
  calc
    _ = ∫ ξ, ‖cutoffKernel t x ξ‖ ^ 2 := norm_toLp_sq (cutoffKernel_memLp t x)
      (cutoffKernel_continuous t x) (cutoffKernel_compact t x)
    _ = ∫ ξ : Space d, cutoff t ξ ^ 2 := by
      apply integral_congr_ae
      exact ae_of_all _ fun ξ => by
        simp [cutoffKernel, phase_norm, Real.norm_of_nonneg (cutoff_nonneg t ξ)]
    _ ≤ _ := cutoff_sq_integral_le (d := d) t

private theorem finiteBessel {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {N : ℕ} {v : Fin N → H} (hv : Orthonormal ℂ v) (g : H) :
    ∑ i, ‖⟪v i, g⟫‖ ^ 2 ≤ ‖g‖ ^ 2 :=
  Orthonormal.sum_inner_products_le (s := Finset.univ) g hv

private theorem low_sum_le {d N : ℕ} {f : Fin N → 𝓢(Space d, ℂ)}
    (hf : Orthonormal ℂ (fun i => (𝓕 (f i)).toLp 2 volume)) (t : ℝ) (x : Space d) :
    ∑ i, ‖low t (f i) x‖ ^ 2 ≤ volume.real (Metric.ball (0 : Space d) (Real.sqrt t)) := by
  calc
    _ = ∑ i : Fin N, ‖⟪(𝓕 (f i)).toLp 2 volume, cutoffKernelLp t x⟫‖ ^ 2 := by
      simp only [low_norm_eq_inner_norm]
    _ ≤ ‖cutoffKernelLp t x‖ ^ 2 := by
      have h := finiteBessel hf (cutoffKernelLp t x)
      exact h
    _ ≤ _ := cutoffKernelLp_norm_le t x

private theorem norm_sq_integrable {d : ℕ} (f : 𝓢(Space d, ℂ)) :
    Integrable (fun x => ‖f x‖ ^ 2) := by
  exact (f.memLp 2 volume).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)

private theorem derivative_energy {d : ℕ} (f : 𝓢(Space d, ℂ)) :
    Integrable (fun ξ => ‖ξ‖ ^ 2 * ‖𝓕 f ξ‖ ^ 2) ∧
    (2 * Real.pi) ^ 2 * (∫ ξ, ‖ξ‖ ^ 2 * ‖𝓕 f ξ‖ ^ 2) =
      ∫ x, ∑ k, ‖fderiv ℝ f x (EuclideanSpace.single k 1)‖ ^ 2 := by
  let v (k : Fin d) : Space d := EuclideanSpace.single k 1
  have hξ (ξ : Space d) (k : Fin d) :
      ‖𝓕 (∂_{v k} f) ξ‖ ^ 2 = (2 * Real.pi) ^ 2 * (ξ k ^ 2 * ‖𝓕 f ξ‖ ^ 2) := by
    rw [fourier_lineDerivOp_eq, smul_apply, smulLeftCLM_apply_apply (by fun_prop)]
    simp [v, EuclideanSpace.inner_single_right, mul_pow,
      Real.norm_of_nonneg Real.pi_pos.le, mul_assoc, mul_left_comm]
  have hsum (ξ : Space d) :
      ∑ k, ‖𝓕 (∂_{v k} f) ξ‖ ^ 2 = (2 * Real.pi) ^ 2 * (‖ξ‖ ^ 2 * ‖𝓕 f ξ‖ ^ 2) := by
    simp [hξ, EuclideanSpace.real_norm_sq_eq, Finset.sum_mul, Finset.mul_sum]
  have hInt :
      Integrable (fun ξ : Space d => ∑ k, ‖𝓕 (∂_{v k} f) ξ‖ ^ 2) :=
    integrable_finsetSum _ fun k _ => norm_sq_integrable (𝓕 (∂_{v k} f))
  have hC : (2 * Real.pi) ^ 2 ≠ 0 := by positivity
  refine ⟨?_, ?_⟩
  · simp_rw [hsum] at hInt
    have h := hInt.const_mul ((2 * Real.pi) ^ 2)⁻¹
    simpa only [← mul_assoc, inv_mul_cancel₀ hC, one_mul] using h
  · rw [← integral_const_mul]
    simp_rw [← hsum, ← lineDerivOp_apply_eq_fderiv]
    rw [integral_finsetSum _ (fun k _ => norm_sq_integrable (𝓕 (∂_{v k} f))),
      integral_finsetSum _ (fun k _ => norm_sq_integrable (∂_{v k} f))]
    simp only [integral_norm_sq_fourier]

private def highFrequency {d : ℕ} (t : ℝ) (f : 𝓢(Space d, ℂ)) : 𝓢(Space d, ℂ) :=
  𝓕 f - lowFrequency t (𝓕 f)

private theorem highFrequency_apply {d : ℕ} (t : ℝ) (f : 𝓢(Space d, ℂ)) (ξ : Space d) :
    highFrequency t f ξ = ((1 - cutoff t ξ : ℝ) : ℂ) * 𝓕 f ξ := by
  simp [highFrequency, lowFrequency_apply, sub_mul]

private theorem high_plancherel {d : ℕ} (t : ℝ) (f : 𝓢(Space d, ℂ)) :
    ∫⁻ x, ENNReal.ofReal (‖high t f x‖ ^ 2) =
      ∫⁻ ξ, ENNReal.ofReal (‖highFrequency t f ξ‖ ^ 2) := by
  have h : ∀ x, high t f x = 𝓕⁻ (highFrequency t f) x := by
    intro x
    simp [high, low, highFrequency, fourierInv_sub]
  simp_rw [h]
  rw [← ofReal_integral_eq_lintegral_ofReal (norm_sq_integrable (𝓕⁻ (highFrequency t f)))
      (ae_of_all _ fun _ => sq_nonneg _),
    ← ofReal_integral_eq_lintegral_ofReal (norm_sq_integrable (highFrequency t f))
      (ae_of_all _ fun _ => sq_nonneg _),
    ← integral_norm_sq_fourier (𝓕⁻ (highFrequency t f)), fourier_fourierInv_eq]

private theorem highFrequency_measurable {d : ℕ} (f : 𝓢(Space d, ℂ)) :
    Measurable (fun p : ℝ × Space d => highFrequency p.1 f p.2) := by
  simp_rw [highFrequency_apply]
  exact (Complex.continuous_ofReal.measurable.comp
    (measurable_const.sub cutoff_measurable)).mul
    ((𝓕 f).continuous.measurable.comp measurable_snd)

private theorem high_integral_le {d : ℕ} (f : 𝓢(Space d, ℂ)) :
    (∫⁻ x, ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (‖high t f x‖ ^ 2)) ≤
      ENNReal.ofReal (2 * ∫ ξ, ‖ξ‖ ^ 2 * ‖𝓕 f ξ‖ ^ 2) := by
  rw [lintegral_lintegral_swap (by
    exact ((high_measurable f).norm.pow_const 2).ennreal_ofReal.aemeasurable)]
  simp_rw [high_plancherel]
  rw [lintegral_lintegral_swap (by
    exact ((highFrequency_measurable f).norm.pow_const 2).ennreal_ofReal.aemeasurable)]
  rw [← integral_const_mul, ofReal_integral_eq_lintegral_ofReal
    ((derivative_energy f).1.const_mul 2) (ae_of_all _ fun _ => by positivity)]
  apply lintegral_mono
  intro ξ
  let s := Ioc 0 (2 * ‖ξ‖ ^ 2)
  have hs (t : ℝ) (ht : t ∈ Ioi (0 : ℝ)) :
      ENNReal.ofReal (‖highFrequency t f ξ‖ ^ 2) ≤
        s.indicator (fun _ => ENNReal.ofReal (‖𝓕 f ξ‖ ^ 2)) t := by
    by_cases ht' : t ∈ s
    · rw [indicator_of_mem ht', highFrequency_apply, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (sub_nonneg.mpr (cutoff_le_one t ξ))]
      apply ENNReal.ofReal_le_ofReal
      apply (sq_le_sq₀ (mul_nonneg (sub_nonneg.mpr (cutoff_le_one t ξ))
        (norm_nonneg _)) (norm_nonneg _)).2
      exact mul_le_of_le_one_left (norm_nonneg _) (sub_le_self _ (cutoff_nonneg t ξ))
    · have htle : 2 * ‖ξ‖ ^ 2 ≤ t := le_of_not_ge (fun h => ht' ⟨ht, h⟩)
      rw [indicator_of_notMem ht', highFrequency_apply, cutoff_one ht htle]
      simp
  calc
    _ ≤ ∫⁻ t in Ioi (0 : ℝ), s.indicator (fun _ => ENNReal.ofReal (‖𝓕 f ξ‖ ^ 2)) t :=
      lintegral_mono_ae ((ae_restrict_mem measurableSet_Ioi).mono hs)
    _ ≤ ∫⁻ t, s.indicator (fun _ => ENNReal.ofReal (‖𝓕 f ξ‖ ^ 2)) t :=
      lintegral_mono' Measure.restrict_le_self (le_refl _)
    _ = _ := by
      rw [lintegral_indicator_const measurableSet_Ioc, Real.volume_Ioc, sub_zero,
        ← ENNReal.ofReal_mul (sq_nonneg _)]
      ring_nf

private def unitVolume (d : ℕ) : ℝ := volume.real (Metric.ball (0 : Space d) 1)

private theorem unitVolume_pos (d : ℕ) : 0 < unitVolume d :=
  ENNReal.toReal_pos (Metric.measure_ball_pos volume _ zero_lt_one).ne' measure_ball_lt_top.ne

private theorem volume_sqrt_ball {d : ℕ} {t : ℝ} (ht : 0 < t) :
    volume.real (Metric.ball (0 : Space d) (Real.sqrt t)) = unitVolume d * t ^ ((d : ℝ) / 2) := by
  rw [measureReal_def, Measure.addHaar_ball_of_pos _ _ (Real.sqrt_pos.2 ht), ENNReal.toReal_mul,
    finrank_euclideanSpace_fin, ENNReal.toReal_ofReal (by positivity),
    Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul ht.le]
  rw [show (1 / (2 : ℝ)) * d = d / 2 by ring]
  exact mul_comm _ _

private def densityConstant (d : ℕ) : ℝ := (1 / 4) / (4 * unitVolume d) ^ (2 / (d : ℝ))

private theorem densityConstant_pos (d : ℕ) : 0 < densityConstant d := by
  have := unitVolume_pos d
  unfold densityConstant
  positivity

private def density {d N : ℕ} (f : Fin N → 𝓢(Space d, ℂ)) (x : Space d) : ℝ :=
  ∑ i, ‖f i x‖ ^ 2

private def highDensity {d N : ℕ} (f : Fin N → 𝓢(Space d, ℂ)) (t : ℝ) (x : Space d) : ℝ :=
  ∑ i, ‖high t (f i) x‖ ^ 2

private theorem density_le {d N : ℕ} (f : Fin N → 𝓢(Space d, ℂ)) (t : ℝ) (x : Space d) :
    density f x ≤ 2 * (∑ i, ‖low t (f i) x‖ ^ 2) + 2 * highDensity f t x := by
  unfold density highDensity
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  have h := norm_add_le (low t (f i) x) (high t (f i) x)
  have heq : low t (f i) x + high t (f i) x = f i x := by simp [high]
  rw [heq] at h
  have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 h
  nlinarith [sq_nonneg (‖low t (f i) x‖ - ‖high t (f i) x‖)]

private theorem density_integral_le {d N : ℕ} (hd : 0 < d) {f : Fin N → 𝓢(Space d, ℂ)}
    (hf : Orthonormal ℂ (fun i => (𝓕 (f i)).toLp 2 volume)) (x : Space d) :
    ENNReal.ofReal (densityConstant d * density f x ^ (1 + 2 / (d : ℝ))) ≤
      ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (highDensity f t x) := by
  let ρ := density f x
  have hρ : 0 ≤ ρ := Finset.sum_nonneg fun _ _ => sq_nonneg _
  let c := unitVolume d
  have hc : 0 < c := unitVolume_pos d
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  let τ := (ρ / (4 * c)) ^ (2 / (d : ℝ))
  have hτ : 0 ≤ τ := Real.rpow_nonneg (by positivity) _
  have hτpow : τ ^ ((d : ℝ) / 2) = ρ / (4 * c) := by
    dsimp only [τ]
    rw [← Real.rpow_mul (by positivity), div_mul_div_comm, mul_comm 2, div_self (by positivity),
      Real.rpow_one]
  have hbound (t : ℝ) (ht : t ∈ Ioc 0 τ) : ρ / 4 ≤ highDensity f t x := by
    have hlow := low_sum_le hf t x
    rw [volume_sqrt_ball ht.1] at hlow
    have hpow := Real.rpow_le_rpow ht.1.le ht.2 (by positivity : 0 ≤ (d : ℝ) / 2)
    rw [hτpow] at hpow
    have hmul := mul_le_mul_of_nonneg_left hpow hc.le
    have hcancel : c * (ρ / (4 * c)) = ρ / 4 := by field_simp
    change c * t ^ ((d : ℝ) / 2) ≤ c * (ρ / (4 * c)) at hmul
    rw [hcancel] at hmul
    have htotal := density_le f t x
    change ρ ≤ _ at htotal
    change ∑ i, ‖low t (f i) x‖ ^ 2 ≤ c * t ^ ((d : ℝ) / 2) at hlow
    linarith
  have hproduct : densityConstant d * ρ ^ (1 + 2 / (d : ℝ)) = ρ / 4 * τ := by
    rw [Real.rpow_add_of_nonneg hρ zero_le_one (by positivity), Real.rpow_one]
    dsimp only [densityConstant, τ, c]
    rw [Real.div_rpow hρ (by positivity)]
    ring
  change ENNReal.ofReal (densityConstant d * ρ ^ (1 + 2 / (d : ℝ))) ≤ _
  rw [hproduct, ENNReal.ofReal_mul (by positivity),
    ← sub_zero τ, ← Real.volume_Ioc, ← setLIntegral_const]
  exact (lintegral_mono_ae ((ae_restrict_mem measurableSet_Ioc).mono fun t ht =>
    ENNReal.ofReal_le_ofReal (hbound t ht))).trans
    (lintegral_mono_set (fun _ ht => ht.1))

private theorem highDensity_integral_eq {d N : ℕ} (f : Fin N → 𝓢(Space d, ℂ)) :
    (∫⁻ x, ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (highDensity f t x)) =
      ∑ i, ∫⁻ x, ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (‖high t (f i) x‖ ^ 2) := by
  let μ := (volume : Measure ℝ).restrict (Ioi 0)
  let H (i : Fin N) (x : Space d) (t : ℝ) := ENNReal.ofReal (‖high t (f i) x‖ ^ 2)
  have hH (i : Fin N) : Measurable (Function.uncurry (H i)) :=
    ((high_measurable (f i)).norm.pow_const 2).ennreal_ofReal
  have hinner (x : Space d) :
      (∫⁻ t, ENNReal.ofReal (highDensity f t x) ∂μ) = ∑ i, ∫⁻ t, H i x t ∂μ := by
    have ht (t : ℝ) : ENNReal.ofReal (highDensity f t x) = ∑ i, H i x t :=
      ENNReal.ofReal_sum_of_nonneg (fun i _ => sq_nonneg ‖high t (f i) x‖)
    exact (lintegral_congr ht).trans (lintegral_finsetSum _ (f := fun i => H i x) fun i _ =>
      (hH i).comp (measurable_const.prodMk measurable_id : Measurable (fun t : ℝ => (x, t))))
  exact (lintegral_congr hinner).trans
    (lintegral_finsetSum _ (f := fun i x => ∫⁻ t, H i x t ∂μ) fun i _ =>
      Measurable.lintegral_prod_right (f := H i) (hH i))


/-- **Lieb–Thirring kinetic energy inequality.** For every dimension `d ≥ 1` there is a constant
`K > 0` such that for every `N` and every family `u_1, …, u_N` of smooth compactly supported
complex functions on `ℝ^d` that is orthonormal in `L²(ℝ^d)`,
`K ∫ (∑_n |u_n|²)^{1 + 2/d} ≤ ∑_n ∫ |∇u_n|²`, where `|∇u|² = ∑_k |∂_k u|²`
(R. L. Frank, *The Lieb–Thirring inequalities: recent results and open problems*,
arXiv:2007.09326v1, July 17, 2020 preprint, Theorem 1; E. H. Lieb and W. Thirring, Phys. Rev.
Lett. 35 (1975) 687–689). This is Frank's Theorem 1 restricted from `H¹(ℝ^d)` to smooth compactly
supported functions, hence a weaker statement. -/
theorem lieb_thirring_kinetic (d : ℕ) (hd : 1 ≤ d) :
    ∃ K : ℝ, 0 < K ∧ ∀ (N : ℕ) (u : Fin N → EuclideanSpace ℝ (Fin d) → ℂ),
      (∀ i, ContDiff ℝ ∞ (u i)) → (∀ i, HasCompactSupport (u i)) →
      (∀ i j, ∫ x, star (u i x) * u j x = if i = j then 1 else 0) →
      K * ∫ x, (∑ i, ‖u i x‖ ^ 2) ^ (1 + 2 / (d : ℝ)) ≤
        ∑ i, ∫ x, ∑ k, ‖fderiv ℝ (u i) x (EuclideanSpace.single k 1)‖ ^ 2 := by
  classical
  let a := 2 / (2 * Real.pi) ^ 2
  have ha : 0 < a := by dsimp [a]; positivity
  refine ⟨densityConstant d / a, div_pos (densityConstant_pos d) ha, ?_⟩
  intro N u hu huc huo
  let f (i : Fin N) : 𝓢(Space d, ℂ) := (huc i).toSchwartzMap (hu i)
  have hf : Orthonormal ℂ (fun i => (𝓕 (f i)).toLp 2 volume) := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [inner_fourier_toL2_eq, SchwartzMap.toLp, SchwartzMap.toLp, inner_toLp]
    exact huo i j
  let kinetic (i : Fin N) : ℝ :=
    ∫ x, ∑ k, ‖fderiv ℝ (u i) x (EuclideanSpace.single k 1)‖ ^ 2
  have kinetic_nonneg (i : Fin N) : 0 ≤ kinetic i :=
    integral_nonneg fun _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  let p := 1 + 2 / (d : ℝ)
  have hbound :
      (∫⁻ x, ENNReal.ofReal (densityConstant d * density f x ^ p)) ≤
        ENNReal.ofReal (a * ∑ i, kinetic i) := calc
    _ ≤ ∫⁻ x, ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (highDensity f t x) :=
      lintegral_mono (density_integral_le hd hf)
    _ = _ := highDensity_integral_eq f
    _ ≤ ∑ i, ENNReal.ofReal (2 * ∫ ξ, ‖ξ‖ ^ 2 * ‖𝓕 (f i) ξ‖ ^ 2) :=
      Finset.sum_le_sum fun i _ => high_integral_le (f i)
    _ = _ := by
      rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg (fun i _ =>
        mul_nonneg ha.le (kinetic_nonneg i))]
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      have he := (derivative_energy (f i)).2
      change (2 * Real.pi) ^ 2 * (∫ ξ, ‖ξ‖ ^ 2 * ‖𝓕 (f i) ξ‖ ^ 2) = kinetic i at he
      rw [← he]
      dsimp [a]
      field_simp
  have hnonneg : 0 ≤ᵐ[volume] (fun x => densityConstant d * density f x ^ p) :=
    ae_of_all _ fun x => mul_nonneg (densityConstant_pos d).le
      (Real.rpow_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) _)
  have hmeas : Continuous (fun x => densityConstant d * density f x ^ p) := by
    have hρ : Continuous (density f) :=
      continuous_finsetSum _ fun i _ => (f i).continuous.norm.pow 2
    exact continuous_const.mul (hρ.rpow_const fun _ => Or.inr (by dsimp [p]; positivity))
  have hint : Integrable (fun x => densityConstant d * density f x ^ p) :=
    ⟨hmeas.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal hnonneg).2
      (hbound.trans_lt ENNReal.ofReal_lt_top)⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnonneg, integral_const_mul] at hbound
  have hreal := (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg ha.le (Finset.sum_nonneg fun i _ => kinetic_nonneg i))).1 hbound
  change densityConstant d / a * (∫ x, density f x ^ p) ≤ ∑ i, kinetic i
  rw [div_mul_eq_mul_div]
  exact (div_le_iff₀ ha).2 (by simpa only [mul_comm a] using hreal)

end MathlibExt.Analysis.FunctionSpaces.LiebThirringWanted
