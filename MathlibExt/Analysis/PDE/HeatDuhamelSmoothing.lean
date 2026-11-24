/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.PDE.HeatDuhamel
public import MathlibExt.Analysis.PDE.HeatKernelGradient
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# First spatial smoothing of heat-kernel Duhamel integrals

Continuous forcing with uniform exponential spatial growth acquires one spatial
derivative after Duhamel integration. A square-root change of time variable
cancels the integrable first-kernel-derivative singularity. No derivative of the
forcing is assumed.

The Duhamel construction is the one in James Nolen, *Partial Differential
Equations and Diffusion Processes*, §2.4, formula (4.42),
https://math.stanford.edu/~ryzhik/STANFORD/STANF227-10/notes227-09.pdf.
The first-derivative conclusion here is proved for continuous, exponentially
growing forcing using Gaussian first-moment domination. It does not assert
that such forcing has the two spatial derivatives of the classical theorem.
-/

@[expose] public section

open MeasureTheory Set Real Filter Topology
open MathlibExt.Analysis

namespace MathlibExt.Analysis.PDE.HeatKernel

private theorem continuous_firstMoment_family {f : ℝ → ℝ → ℝ}
    (hf : Continuous (Function.uncurry f)) {M c : ℝ} (hM : 0 ≤ M) (hc : 0 ≤ c)
    (hb : ∀ s x, |f s x| ≤ M * exp (c * |x|)) :
    Continuous (fun p : (ℝ × ℝ) × ℝ =>
      ∫ y : ℝ, y * heatKernel ℝ 1 y * f p.1.1 (p.2 - p.1.2 * y)) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  have hg : HasExpGrowth (fun x => M * exp (c * |x|)) :=
    ⟨M, c, hM, hc, fun x => by rw [abs_of_nonneg (by positivity)]⟩
  obtain ⟨A, d, _, _, h⟩ := hg.affine_bound (|p.2| + 1) (|p.1.2| + 1)
  have hz : ∀ᶠ q : (ℝ × ℝ) × ℝ in 𝓝 p, |q.2| < |p.2| + 1 :=
    (continuous_snd.abs.tendsto p).eventually_lt_const (lt_add_one _)
  have hs : ∀ᶠ q : (ℝ × ℝ) × ℝ in 𝓝 p, |q.1.2| < |p.1.2| + 1 :=
    ((continuous_snd.comp continuous_fst).abs.tendsto p).eventually_lt_const
      (lt_add_one _)
  refine tendsto_integral_filter_of_dominated_convergence
    (fun y => (|y| * heatKernel ℝ 1 y * exp (d * |y|)) * A) ?_ ?_
    ((integrable_heatKernel_abs_mul_exp_abs one_pos d).mul_const A) ?_
  · filter_upwards with q
    exact ((continuous_id.mul (heatKernel_contDiff 1).continuous).mul
      (hf.comp (continuous_const.prodMk
        (continuous_const.sub (continuous_const.mul continuous_id))))).aestronglyMeasurable
  · filter_upwards [hz, hs] with q hqz hqs
    filter_upwards with y
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (heatKernel_pos one_pos y)]
    have hh := h q.2 q.1.2 y hqz.le hqs.le
    rw [abs_of_nonneg (by positivity)] at hh
    calc
      _ ≤ |y| * heatKernel ℝ 1 y * (A * exp (d * |y|)) :=
        mul_le_mul_of_nonneg_left ((hb _ _).trans hh)
          (mul_nonneg (abs_nonneg y) (heatKernel_pos one_pos y).le)
      _ = _ := by ring
  · filter_upwards with y
    have hy : Continuous (fun q : (ℝ × ℝ) × ℝ =>
        y * heatKernel ℝ 1 y * f q.1.1 (q.2 - q.1.2 * y)) :=
      continuous_const.mul (hf.comp
        ((continuous_fst.comp continuous_fst).prodMk
          (continuous_snd.sub
            ((continuous_snd.comp continuous_fst).mul continuous_const))))
    exact hy.tendsto p

private def clampForcing (f : ℝ → ℝ → ℝ) (T s x : ℝ) : ℝ :=
  f (max 0 (min T s)) x

private theorem clamp_mem {T : ℝ} (hT : 0 ≤ T) (s : ℝ) :
    max 0 (min T s) ∈ Icc 0 T :=
  ⟨le_max_left _ _, max_le hT (min_le_left _ _)⟩

private theorem clampForcing_eq {f : ℝ → ℝ → ℝ} {T s : ℝ} (hs : s ∈ Icc 0 T) :
    clampForcing f T s = f s := by
  funext x
  change f (max 0 (min T s)) x = f s x
  rw [min_eq_right hs.2, max_eq_right hs.1]

private theorem continuous_clampForcing {f : ℝ → ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hf : ContinuousOn (Function.uncurry f) (Icc 0 T ×ˢ univ)) :
    Continuous (Function.uncurry (clampForcing f T)) := by
  exact hf.comp_continuous
    ((continuous_const.max (continuous_const.min continuous_fst)).prodMk continuous_snd)
    (fun p => ⟨clamp_mem hT p.1, mem_univ _⟩)


private theorem firstMoment_family_continuousOn {f : ℝ → ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hf : ContinuousOn (Function.uncurry f) (Icc 0 T ×ˢ univ))
    (hg : HeatWholeLine.HasExpGrowthOnStrip f T) :
    ContinuousOn (fun p : (ℝ × ℝ) × ℝ =>
      ∫ y : ℝ, y * heatKernel ℝ 1 y * f p.1.1 (p.2 - p.1.2 * y))
      ((Icc 0 T ×ˢ univ) ×ˢ univ) := by
  obtain ⟨M, c, hM, hc, hb⟩ := hg
  have h := continuous_firstMoment_family (continuous_clampForcing hT hf) hM hc
    (fun s x => hb _ (clamp_mem hT s) x)
  apply h.continuousOn.congr
  intro p hp
  dsimp only
  rw [clampForcing_eq hp.1.1]

private theorem sqrt_time_mem {T t r : ℝ} (ht : t ∈ Icc 0 T) (hr : r ∈ Icc 0 1) :
    t * (1 - r ^ 2) ∈ Icc 0 T := by
  have hr2 : r ^ 2 ≤ 1 := by nlinarith [hr.1, hr.2]
  exact ⟨mul_nonneg ht.1 (sub_nonneg.mpr hr2),
    (mul_le_of_le_one_right ht.1 (by nlinarith [sq_nonneg r])).trans ht.2⟩

/-- A square-root change of elapsed time represents the Duhamel integral with
weight `r`. This weight cancels the first heat-gradient singularity. -/
theorem heatDuhamel_sqrt_rescaled {f : ℝ → ℝ → ℝ} {T t : ℝ}
    (hf : ContinuousOn (Function.uncurry f) (Icc 0 T ×ˢ univ))
    (hg : HeatWholeLine.HasExpGrowthOnStrip f T) (ν : ℝ) (ht : t ∈ Icc 0 T) (x : ℝ) :
    heatDuhamel ν f t x = 2 * t * ∫ r in (0 : ℝ)..1,
      r * heatSolution (f (t * (1 - r ^ 2))) (ν * t * r ^ 2) x := by
  have hcont : ContinuousOn (fun s => heatSolution (f s) (ν * (t - s)) x) (Icc 0 t) :=
    (heatSolution_family_continuousOn (ht.1.trans ht.2) hf hg).comp
      ((continuous_id.prodMk (continuous_const.mul (continuous_const.sub continuous_id))).prodMk
        continuous_const).continuousOn
      (fun s hs => ⟨⟨⟨hs.1, hs.2.trans ht.2⟩, mem_univ _⟩, mem_univ _⟩)
  have hsub := intervalIntegral.integral_comp_mul_deriv'
    (a := (0 : ℝ)) (b := 1) (f := fun r : ℝ => t * (1 - r ^ 2))
    (f' := fun r => -(2 * t) * r)
    (g := fun s => heatSolution (f s) (ν * (t - s)) x) ?_ ?_ ?_
  · simp only [zero_pow (by decide : 2 ≠ 0), sub_zero, mul_one, one_pow,
      sub_self, mul_zero] at hsub
    have he : (∫ r in (0 : ℝ)..1,
        heatSolution (f (t * (1 - r ^ 2))) (ν * (t - t * (1 - r ^ 2))) x * (-(2 * t)*r)) =
        -(2 * t) * ∫ r in (0 : ℝ)..1,
          r * heatSolution (f (t * (1 - r ^ 2))) (ν * t * r ^ 2) x := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro r _
      dsimp only
      rw [show ν * (t - t * (1 - r ^ 2)) = ν * t * r ^ 2 by ring]
      ring
    dsimp only [Function.comp_def] at hsub
    rw [he, intervalIntegral.integral_symm 0 t] at hsub
    change _ = -heatDuhamel ν f t x at hsub
    linarith
  · intro r _
    convert (((hasDerivAt_const r (1 : ℝ)).sub ((hasDerivAt_id r).pow 2)).const_mul t) using 1 <;>
      dsimp; ring
  · exact (by fun_prop : Continuous (fun r : ℝ => -(2 * t)*r)).continuousOn
  · apply hcont.mono
    rintro _ ⟨r,hr,rfl⟩
    have hr' : r ∈ Icc (0 : ℝ) 1 := by simpa [uIcc_of_le zero_le_one] using hr
    exact sqrt_time_mem (T := t) ⟨ht.1,le_rfl⟩ hr'

private theorem moment_integrand_continuousOn {f : ℝ → ℝ → ℝ} {T t : ℝ}
    (hf : ContinuousOn (Function.uncurry f) (Icc 0 T ×ˢ univ))
    (hg : HeatWholeLine.HasExpGrowthOnStrip f T) (ht : t ∈ Icc 0 T) (ν x : ℝ) :
    ContinuousOn (fun r : ℝ => ∫ y : ℝ, y * heatKernel ℝ 1 y *
      f (t * (1 - r ^ 2)) (x - (sqrt (ν * t) * r) * y)) (Icc 0 1) := by
  exact (firstMoment_family_continuousOn (ht.1.trans ht.2) hf hg).comp
    (((continuous_const.mul (continuous_const.sub (continuous_id.pow 2))).prodMk
      (continuous_const.mul continuous_id)).prodMk continuous_const).continuousOn
    (fun r hr => ⟨⟨sqrt_time_mem ht hr, mem_univ _⟩, mem_univ _⟩)

/-- Merely continuous forcing of uniform exponential growth has a spatially
differentiable Duhamel integral, including at initial time. The formula uses a
fixed time interval and fixed Gaussian and assumes strictly positive viscosity. -/
theorem heatDuhamel_hasDerivAt_space_of_continuous {f : ℝ → ℝ → ℝ} {ν T t : ℝ}
    (hν : 0 < ν) (hf : ContinuousOn (Function.uncurry f) (Icc 0 T ×ˢ univ))
    (hg : HeatWholeLine.HasExpGrowthOnStrip f T) (ht : t ∈ Icc 0 T) (x : ℝ) :
    HasDerivAt (heatDuhamel ν f t)
      (-(sqrt t / sqrt ν) * ∫ r in (0 : ℝ)..1, ∫ y : ℝ,
        y * heatKernel ℝ 1 y * f (t * (1 - r ^ 2)) (x - (sqrt (ν * t) * r) * y)) x := by
  rcases ht.1.eq_or_lt with hzero | htpos
  · subst t
    have he : heatDuhamel ν f 0 = fun _ => 0 := funext (heatDuhamel_zero_time ν f)
    simpa only [he, sqrt_zero, zero_div, neg_zero, zero_mul] using
      (hasDerivAt_const x (0 : ℝ))
  have hT : 0 ≤ T := ht.1.trans ht.2
  have hv : 0 < sqrt (ν * t) := sqrt_pos.mpr (mul_pos hν htpos)
  obtain ⟨M, c, hM, hc, hb⟩ := hg
  let J := ∫ y : ℝ, |y| * heatKernel ℝ 1 y * exp (c * sqrt (ν * t) * |y|)
  have hJ : 0 ≤ J := integral_nonneg (fun y => by
    exact mul_nonneg (mul_nonneg (abs_nonneg y) (heatKernel_pos one_pos y).le) (exp_pos _).le)
  let C := (1 / (2 * sqrt (ν * t))) * ((M * exp (c * (|x| + 1))) * J)
  have hF (z : ℝ) : IntervalIntegrable (fun r : ℝ =>
      r * heatSolution (f (t * (1 - r ^ 2))) (ν * t * r ^ 2) z) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le zero_le_one]
    apply continuousOn_id.mul
    exact (heatSolution_family_continuousOn hT hf ⟨M, c, hM, hc, hb⟩).comp
      (((continuous_const.mul (continuous_const.sub (continuous_id.pow 2))).prodMk
        (continuous_const.mul (continuous_id.pow 2))).prodMk continuous_const).continuousOn
      (fun r hr => ⟨⟨sqrt_time_mem ht hr, mem_univ _⟩, mem_univ _⟩)
  have hG (z : ℝ) : IntervalIntegrable (fun r : ℝ =>
      -(1 / (2 * sqrt (ν * t))) * ∫ y : ℝ, y * heatKernel ℝ 1 y *
        f (t * (1 - r ^ 2)) (z - (sqrt (ν * t) * r) * y)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le zero_le_one]
    exact continuousOn_const.mul (moment_integrand_continuousOn hf ⟨M, c, hM, hc, hb⟩ ht ν z)
  have hresult := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioc 0 1))
    (F := fun z r => r * heatSolution (f (t * (1 - r ^ 2))) (ν * t * r ^ 2) z)
    (F' := fun z r => -(1 / (2 * sqrt (ν * t))) * ∫ y : ℝ, y * heatKernel ℝ 1 y *
      f (t * (1 - r ^ 2)) (z - (sqrt (ν * t) * r) * y))
    (s := Metric.ball x 1) (bound := fun _ => C)
    (Metric.ball_mem_nhds x (by norm_num))
    (Eventually.of_forall (fun z => (hF z).1.aestronglyMeasurable)) (hF x).1
    (hG x).1.aestronglyMeasurable ?_ (integrable_const C) ?_
  · have hd := hresult.2.const_mul (2 * t)
    simp only [← intervalIntegral.integral_of_le zero_le_one,
      intervalIntegral.integral_const_mul] at hd
    have hcoeff : (2 * t) * -(1 / (2 * sqrt (ν * t))) = -(sqrt t / sqrt ν) := by
      rw [sqrt_mul hν.le]
      have hn := sqrt_ne_zero'.mpr hν
      have ht' := sqrt_ne_zero'.mpr htpos
      field_simp
      nlinarith [sq_sqrt ht.1]
    rw [← mul_assoc, hcoeff] at hd
    convert hd using 1
    funext z
    exact heatDuhamel_sqrt_rescaled hf ⟨M, c, hM, hc, hb⟩ ν ht z
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    intro z hz
    have hs := sqrt_time_mem ht ⟨hr.1.le, hr.2⟩
    have hfc : Continuous (f (t * (1 - r ^ 2))) := hf.comp_continuous
      (continuous_const.prodMk continuous_id) (fun y => ⟨hs, mem_univ y⟩)
    have hscale : |sqrt (ν * t) * r| ≤ sqrt (ν * t) := by
      rw [abs_of_nonneg (mul_nonneg hv.le hr.1.le)]
      exact mul_le_of_le_one_right hv.le hr.2
    have hh := abs_heatKernel_firstMoment_le_exp_bound hfc hM hc (hb _ hs) hscale z
    have hz' : |z - x| < 1 := by simpa only [Metric.mem_ball, Real.dist_eq] using hz
    have hzR : |z| ≤ |x| + 1 := by
      have hh := abs_add_le (z - x) x
      rw [sub_add_cancel] at hh
      linarith
    rw [Real.norm_eq_abs,abs_mul,abs_neg,abs_of_nonneg (by positivity : 0 ≤ 1 / (2 * sqrt (ν * t)))]
    exact mul_le_mul_of_nonneg_left (hh.trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (exp_le_exp.mpr
          (mul_le_mul_of_nonneg_left hzR hc)) hM) hJ)) (by positivity)
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    intro z _
    have hs := sqrt_time_mem ht ⟨hr.1.le, hr.2⟩
    have hfc : Continuous (f (t * (1 - r ^ 2))) := hf.comp_continuous
      (continuous_const.prodMk continuous_id) (fun y => ⟨hs, mem_univ y⟩)
    have hgr : HasExpGrowth (f (t * (1 - r ^ 2))) := ⟨M, c, hM, hc, hb _ hs⟩
    have hheat : 0 < ν * t * r ^ 2 := mul_pos (mul_pos hν htpos) (sq_pos_of_pos hr.1)
    have hd := (heatSolution_hasDerivAt_space_of_exp_growth hfc.aestronglyMeasurable
      hgr hheat z).const_mul r
    rw [← (heatSolution_hasDerivAt_space_of_exp_growth hfc.aestronglyMeasurable
      hgr hheat z).deriv, heatSolution_deriv_rescaled_of_exp_growth
      hfc.aestronglyMeasurable hgr hheat z] at hd
    have he : sqrt (ν * t * r ^ 2) = sqrt (ν * t) * r := by
      rw [sqrt_mul (mul_pos hν htpos).le, sqrt_sq hr.1.le]
    rw [he] at hd
    rw [← mul_assoc, show r * -(1 / (2*(sqrt (ν * t) * r))) = -(1 / (2 * sqrt (ν * t))) by
      field_simp [hr.1.ne', hv.ne']] at hd
    exact hd

/-- Spatial smoothing has a jointly continuous actual derivative on the entire
closed strip, including its zero initial trace. No forcing derivative is required. -/
theorem heatDuhamel_deriv_continuousOn_of_continuous {f : ℝ → ℝ → ℝ} {ν T : ℝ}
    (hν : 0 < ν) (hT : 0 ≤ T)
    (hf : ContinuousOn (Function.uncurry f) (Icc 0 T ×ˢ univ))
    (hg : HeatWholeLine.HasExpGrowthOnStrip f T) :
    ContinuousOn (fun p : ℝ × ℝ => deriv (heatDuhamel ν f p.1) p.2)
      (Icc 0 T ×ˢ univ) := by
  obtain ⟨M, c, hM, hc, hb⟩ := hg
  have hcglob := continuous_firstMoment_family (continuous_clampForcing hT hf) hM hc
    (fun s x => hb _ (clamp_mem hT s) x)
  have hG : Continuous (fun p : ℝ × ℝ => ∫ r in (0 : ℝ)..1, ∫ y : ℝ,
      y * heatKernel ℝ 1 y * clampForcing f T (p.1*(1 - r ^ 2))
        (p.2 - (sqrt (ν*p.1)*r) * y)) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (s := fun _ => (1 : ℝ)) (a₀ := 0) ?_ continuous_const
    exact hcglob.comp
      ((((continuous_fst.comp continuous_fst).mul
        (continuous_const.sub (continuous_snd.pow 2))).prodMk
        ((continuous_sqrt.comp (continuous_const.mul (continuous_fst.comp continuous_fst))).mul
          continuous_snd)).prodMk (continuous_snd.comp continuous_fst))
  have hres := ((continuous_sqrt.comp continuous_fst).div_const (sqrt ν)).neg.mul hG
  apply hres.continuousOn.congr
  intro p hp
  dsimp only [Pi.mul_apply, Pi.neg_apply, Function.comp_def]
  rw [(heatDuhamel_hasDerivAt_space_of_continuous hν hf ⟨M, c, hM, hc, hb⟩ hp.1 p.2).deriv]
  congr 1
  apply intervalIntegral.integral_congr
  intro r hr
  dsimp only
  rw [clampForcing_eq (sqrt_time_mem hp.1
    (by simpa only [uIcc_of_le zero_le_one] using hr))]

/-- The Duhamel spatial derivative is bounded by a constant times `sqrt t`,
with explicit viscosity and exponential-growth factors. This includes time zero. -/
theorem abs_heatDuhamel_deriv_le {f : ℝ → ℝ → ℝ} {T M c ν : ℝ}
    (hf : ContinuousOn (Function.uncurry f) (Icc 0 T ×ˢ univ)) (hM : 0 ≤ M) (hc : 0 ≤ c)
    (hb : ∀ s ∈ Icc 0 T, ∀ x, |f s x| ≤ M * exp (c * |x|))
    (hν : 0 < ν) {t : ℝ} (ht : t ∈ Icc 0 T) (x : ℝ) :
    |deriv (heatDuhamel ν f t) x| ≤ (M * sqrt t / sqrt ν) *
      (∫ y : ℝ, |y| * heatKernel ℝ 1 y * exp (c * sqrt (ν * T) * |y|)) * exp (c * |x|) := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun r => ∫ y : ℝ, y * heatKernel ℝ 1 y *
      f (t * (1 - r ^ 2)) (x - (sqrt (ν * t) * r) * y))
    (a := (0 : ℝ)) (b := 1) (C := (M * exp (c * |x|)) *
      ∫ y : ℝ, |y| * heatKernel ℝ 1 y * exp (c * sqrt (ν * T) * |y|)) ?_
  · simp only [Real.norm_eq_abs,sub_zero,abs_one,mul_one] at h
    rw [(heatDuhamel_hasDerivAt_space_of_continuous hν hf ⟨M, c, hM, hc, hb⟩ ht x).deriv,
      abs_mul,abs_neg,abs_of_nonneg (by positivity : 0 ≤ sqrt t / sqrt ν)]
    calc
      _ ≤ (sqrt t / sqrt ν) * ((M * exp (c * |x|)) *
          ∫ y : ℝ, |y| * heatKernel ℝ 1 y * exp (c * sqrt (ν * T) * |y|)) :=
        mul_le_mul_of_nonneg_left h (by positivity)
      _ = _ := by ring
  · intro r hr
    have hr' : r ∈ Ioc (0 : ℝ) 1 := by simpa only [uIoc_of_le zero_le_one] using hr
    have hs := sqrt_time_mem ht ⟨hr'.1.le,hr'.2⟩
    have hfc : Continuous (f (t * (1 - r ^ 2))) := hf.comp_continuous
      (continuous_const.prodMk continuous_id) (fun y => ⟨hs, mem_univ y⟩)
    have hscale : |sqrt (ν * t) * r| ≤ sqrt (ν * T) := by
      rw [abs_of_nonneg (mul_nonneg (sqrt_nonneg _) hr'.1.le)]
      exact (mul_le_of_le_one_right (sqrt_nonneg _) hr'.2).trans
        (sqrt_le_sqrt (mul_le_mul_of_nonneg_left ht.2 hν.le))
    simpa only [Real.norm_eq_abs] using
      abs_heatKernel_firstMoment_le_exp_bound hfc hM hc (hb _ hs) hscale x

/-- The spatial derivative gained from continuous forcing has uniform exponential
growth on every finite nonnegative strip, for positive viscosity. -/
theorem heatDuhamel_deriv_hasExpGrowthOnStrip {f : ℝ → ℝ → ℝ} {ν T : ℝ}
    (hν : 0 < ν)
    (hf : ContinuousOn (Function.uncurry f) (Icc 0 T ×ˢ univ))
    (hg : HeatWholeLine.HasExpGrowthOnStrip f T) :
    HeatWholeLine.HasExpGrowthOnStrip (fun t x => deriv (heatDuhamel ν f t) x) T := by
  obtain ⟨M, c, hM, hc, hb⟩ := hg
  let J := ∫ y : ℝ, |y| * heatKernel ℝ 1 y * exp (c * sqrt (ν * T) * |y|)
  have hJ : 0 ≤ J := integral_nonneg (fun y =>
    mul_nonneg (mul_nonneg (abs_nonneg y) (heatKernel_pos one_pos y).le) (exp_pos _).le)
  refine ⟨(M * sqrt T / sqrt ν) * J, c,
    mul_nonneg (div_nonneg (mul_nonneg hM (sqrt_nonneg T)) (sqrt_nonneg ν)) hJ, hc,
    fun t ht x => ?_⟩
  exact (abs_heatDuhamel_deriv_le hf hM hc hb hν ht x).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (sqrt_le_sqrt ht.2) hM) (sqrt_nonneg _)) hJ)
      (exp_pos _).le)

end MathlibExt.Analysis.PDE.HeatKernel
