/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.PDE.HeatKernelContinuity
public import MathlibExt.Analysis.PDE.HeatWholeLine
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# The heat-kernel Duhamel integral

The time integral of the Gaussian heat evolution represents the contribution
of a forcing term with zero initial data. This is the whole-line construction
in Stanford Math 220B, *Heat Equation*, §2.7.2,
https://web.stanford.edu/class/math220b/handouts/heateqn.pdf.

Continuous forcing with a uniform exponential spatial bound has an integrable
time integrand and jointly continuous Duhamel integral, including time zero.
Explicit Gaussian moments give quantitative bounds and preserve exponential
growth on finite strips. Integrability also justifies linearity and comparison.
These growth hypotheses extend the compact-support setting of the reference;
the proofs use fixed-Gaussian domination rather than a bounded-data assumption.

The definition uses the existing stationary extension of `heatSolution` at
nonpositive heat times. Its intended evolution statements concern nonnegative
times and positive viscosity. Continuity and algebraic identities also apply
to the chosen extension at other viscosities; no backward heat equation or
classical PDE for merely continuous forcing is asserted here.
-/

@[expose] public section

open MeasureTheory Set Real Filter Topology
open MathlibExt.Analysis

namespace MathlibExt.Analysis.PDE.HeatKernel

/-- The Gaussian time integral for an inhomogeneous heat equation with zero initial data. -/
noncomputable def heatDuhamel (ν : ℝ) (f : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ :=
  ∫ s in 0..t, heatSolution (f s) (ν * (t - s)) x

/-- The Duhamel integral vanishes at initial time. -/
@[simp] theorem heatDuhamel_zero_time (ν : ℝ) (f : ℝ → ℝ → ℝ) (x : ℝ) :
    heatDuhamel ν f 0 x = 0 := by simp [heatDuhamel]

/-- Spatially constant forcing reduces to its ordinary time integral. -/
theorem heatDuhamel_time_only (ν : ℝ) (f : ℝ → ℝ) (t x : ℝ) :
    heatDuhamel ν (fun s _ => f s) t x = ∫ s in 0..t, f s := by
  simp [heatDuhamel]

/-- Constant forcing accumulates linearly in time. -/
@[simp] theorem heatDuhamel_const (ν c t x : ℝ) :
    heatDuhamel ν (fun _ _ => c) t x = t * c := by
  simp [heatDuhamel]

/-- Scalar multiplication commutes with the time integral. -/
theorem heatDuhamel_const_mul (ν c : ℝ) (f : ℝ → ℝ → ℝ) (t x : ℝ) :
    heatDuhamel ν (fun s y => c * f s y) t x = c * heatDuhamel ν f t x := by
  simp only [heatDuhamel, heatSolution_const_mul, intervalIntegral.integral_const_mul]

/-- Nonnegative forcing on a nonnegative time interval gives a nonnegative integral. -/
theorem heatDuhamel_nonneg (ν : ℝ) {f : ℝ → ℝ → ℝ} {t : ℝ}
    (hf : ∀ s ∈ Icc 0 t, ∀ y, 0 ≤ f s y) (ht : 0 ≤ t) (x : ℝ) :
    0 ≤ heatDuhamel ν f t x := by
  exact intervalIntegral.integral_nonneg ht
    (fun s hs => heatSolution_nonneg (hf s hs) _ x)

/-- A fixed unit time interval and fixed Gaussian represent the same time integral.
The identity includes time zero; no differentiability at that endpoint is asserted. -/
theorem heatDuhamel_rescaled (ν : ℝ) (f : ℝ → ℝ → ℝ) (t x : ℝ) :
    heatDuhamel ν f t x = t * ∫ r in (0 : ℝ)..1,
      ∫ y : ℝ, heatKernel ℝ 1 y * f (t * r) (x - sqrt (ν * (t - t * r)) * y) := by
  have h := intervalIntegral.smul_integral_comp_mul_left
    (fun s => heatSolution (f s) (ν * (t - s)) x) (a := 0) (b := 1) t
  simpa only [heatDuhamel, mul_zero, mul_one, smul_eq_mul,
    heatSolution_rescaled_all] using h.symm

private theorem continuous_heat_family {f : ℝ → ℝ → ℝ}
    (hf : Continuous (Function.uncurry f)) {M c : ℝ} (hM : 0 ≤ M) (hc : 0 ≤ c)
    (hb : ∀ s x, |f s x| ≤ M * exp (c * |x|)) :
    Continuous (fun p : (ℝ × ℝ) × ℝ => heatSolution (f p.1.1) p.1.2 p.2) := by
  simp_rw [heatSolution_rescaled_all]
  apply continuous_iff_continuousAt.mpr
  intro p
  have hg : HasExpGrowth (fun x => M * exp (c * |x|)) :=
    ⟨M, c, hM, hc, fun x => by rw [abs_of_nonneg (by positivity)]⟩
  obtain ⟨A, d, _, _, h⟩ := hg.affine_bound (|p.2| + 1) (|sqrt p.1.2| + 1)
  have hz : ∀ᶠ q : (ℝ × ℝ) × ℝ in 𝓝 p, |q.2| < |p.2| + 1 :=
    (continuous_snd.abs.tendsto p).eventually_lt_const (lt_add_one _)
  have hs : ∀ᶠ q : (ℝ × ℝ) × ℝ in 𝓝 p, |sqrt q.1.2| < |sqrt p.1.2| + 1 :=
    ((continuous_sqrt.comp (continuous_snd.comp continuous_fst)).abs.tendsto p).eventually_lt_const
      (lt_add_one _)
  refine tendsto_integral_filter_of_dominated_convergence
    (fun y => (heatKernel ℝ 1 y * exp (d * |y|)) * A) ?_ ?_
    ((integrable_heatKernel_exp_abs one_pos d).mul_const A) ?_
  · filter_upwards with q
    exact ((heatKernel_contDiff 1).continuous.mul
      (hf.comp (continuous_const.prodMk
        (continuous_const.sub (continuous_const.mul continuous_id))))).aestronglyMeasurable
  · filter_upwards [hz, hs] with q hqz hqs
    filter_upwards with y
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (heatKernel_pos one_pos y)]
    have hh := h q.2 (sqrt q.1.2) y hqz.le hqs.le
    rw [abs_of_nonneg (by positivity)] at hh
    calc
      _ ≤ heatKernel ℝ 1 y * (A * exp (d * |y|)) :=
        mul_le_mul_of_nonneg_left ((hb _ _).trans hh) (heatKernel_pos one_pos y).le
      _ = _ := by ring
  · filter_upwards with y
    have hy : Continuous (fun q : (ℝ × ℝ) × ℝ =>
        heatKernel ℝ 1 y * f q.1.1 (q.2 - sqrt q.1.2 * y)) :=
      continuous_const.mul (hf.comp
        ((continuous_fst.comp continuous_fst).prodMk
          (continuous_snd.sub
            ((continuous_sqrt.comp (continuous_snd.comp continuous_fst)).mul continuous_const))))
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

private theorem continuous_clamped_integrand {f : ℝ → ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hf : ContinuousOn (Function.uncurry f) (Icc 0 T ×ˢ univ))
    (hg : HeatWholeLine.HasExpGrowthOnStrip f T) (ν : ℝ) :
    Continuous (fun p : (ℝ × ℝ) × ℝ =>
      heatSolution (clampForcing f T p.2) (ν * (p.1.1 - p.2)) p.1.2) := by
  obtain ⟨M, c, hM, hc, hb⟩ := hg
  have h := continuous_heat_family (continuous_clampForcing hT hf) hM hc
    (fun s x => hb _ (clamp_mem hT s) x)
  exact h.comp ((continuous_snd.prodMk
    (continuous_const.mul ((continuous_fst.comp continuous_fst).sub continuous_snd))).prodMk
      (continuous_snd.comp continuous_fst))

/-- The heat evolution of a continuous, uniformly exponentially bounded family is
jointly continuous in its family parameter, heat time, and spatial position. Heat
time may be nonpositive, using the stationary extension. -/
theorem heatSolution_family_continuousOn {f : ℝ → ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hf : ContinuousOn (Function.uncurry f) (Icc 0 T ×ˢ univ))
    (hg : HeatWholeLine.HasExpGrowthOnStrip f T) :
    ContinuousOn (fun p : (ℝ × ℝ) × ℝ => heatSolution (f p.1.1) p.1.2 p.2)
      ((Icc 0 T ×ˢ univ) ×ˢ univ) := by
  obtain ⟨M, c, hM, hc, hb⟩ := hg
  have h := continuous_heat_family (continuous_clampForcing hT hf) hM hc
    (fun s x => hb _ (clamp_mem hT s) x)
  apply h.continuousOn.congr
  intro p hp
  dsimp only
  rw [clampForcing_eq hp.1.1]

/-- Continuous forcing with uniform exponential growth has an integrable time integrand
at each point of a closed nonnegative strip. -/
theorem intervalIntegrable_heatDuhamel {f : ℝ → ℝ → ℝ} {T : ℝ}
    (hf : ContinuousOn (Function.uncurry f) (Icc 0 T ×ˢ univ))
    (hg : HeatWholeLine.HasExpGrowthOnStrip f T) (ν : ℝ) {t : ℝ}
    (ht : t ∈ Icc 0 T) (x : ℝ) :
    IntervalIntegrable (fun s => heatSolution (f s) (ν * (t - s)) x) volume 0 t := by
  have hcont : Continuous
      (fun s => heatSolution (clampForcing f T s) (ν * (t - s)) x) :=
    (continuous_clamped_integrand (ht.1.trans ht.2) hf hg ν).comp
      ((continuous_const (y := (t, x))).prodMk continuous_id)
  have h := hcont.intervalIntegrable (μ := volume) 0 t
  apply h.congr
  intro s hs
  have hs₁ : s ∈ Ioc 0 t := by simpa [uIoc_of_le ht.1] using hs
  have hs' : s ∈ Icc 0 T := ⟨hs₁.1.le, hs₁.2.trans ht.2⟩
  dsimp only
  rw [clampForcing_eq (f := f) hs']

/-- The Duhamel integral is jointly continuous on a closed time strip for continuous
forcing of uniform exponential growth, including the zero initial trace. -/
theorem heatDuhamel_continuousOn {f : ℝ → ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hf : ContinuousOn (Function.uncurry f) (Icc 0 T ×ˢ univ))
    (hg : HeatWholeLine.HasExpGrowthOnStrip f T) (ν : ℝ) :
    ContinuousOn (Function.uncurry (heatDuhamel ν f)) (Icc 0 T ×ˢ univ) := by
  have h : Continuous (fun p : ℝ × ℝ => heatDuhamel ν (clampForcing f T) p.1 p.2) := by
    unfold heatDuhamel
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (continuous_clamped_integrand hT hf hg ν) continuous_fst
  apply h.continuousOn.congr
  intro p hp
  unfold heatDuhamel Function.uncurry
  apply intervalIntegral.integral_congr
  intro s hs
  have hs₁ : s ∈ Icc 0 p.1 := by simpa [uIcc_of_le hp.1.1] using hs
  have hs' : s ∈ Icc 0 T := ⟨hs₁.1, hs₁.2.trans hp.1.2⟩
  dsimp only
  rw [clampForcing_eq (f := f) hs']

/-- An explicit Gaussian moment controls heat evolution of exponentially bounded data
uniformly for heat times at most `H`, including the stationary extension. -/
theorem abs_heatSolution_le_exp_bound {f : ℝ → ℝ} (hf : Continuous f)
    {M c : ℝ} (hM : 0 ≤ M) (hc : 0 ≤ c) (hb : ∀ x, |f x| ≤ M * exp (c * |x|))
    {s H : ℝ} (hs : s ≤ H) (x : ℝ) :
    |heatSolution f s x| ≤ M *
      (∫ y : ℝ, heatKernel ℝ 1 y * exp (c * sqrt H * |y|)) * exp (c * |x|) := by
  have hsq : |sqrt s| ≤ sqrt H := by
    rw [abs_of_nonneg (sqrt_nonneg _)]
    exact sqrt_le_sqrt hs
  have hbound (y : ℝ) : |f (x - sqrt s * y)| ≤
      (M * exp (c * |x|)) * exp (c * sqrt H * |y|) := by
    have ha : |x - sqrt s * y| ≤ |x| + sqrt H * |y| :=
      (abs_sub _ _).trans (add_le_add le_rfl
        (by simpa only [abs_mul] using mul_le_mul_of_nonneg_right hsq (abs_nonneg y)))
    calc
      _ ≤ M * exp (c * |x - sqrt s * y|) := hb _
      _ ≤ M * exp (c * (|x| + sqrt H * |y|)) :=
        mul_le_mul_of_nonneg_left (exp_le_exp.mpr (mul_le_mul_of_nonneg_left ha hc)) hM
      _ = _ := by simp only [mul_add, exp_add, mul_assoc]
  rw [heatSolution_rescaled_all]
  have hi := integrable_heatKernel_mul_affine hf ⟨M, c, hM, hc, hb⟩ x (sqrt s)
  calc
    _ ≤ ∫ y, |heatKernel ℝ 1 y * f (x - sqrt s * y)| :=
      MeasureTheory.abs_integral_le_integral_abs
    _ ≤ ∫ y, (M * exp (c * |x|)) * (heatKernel ℝ 1 y * exp (c * sqrt H * |y|)) := by
      apply integral_mono (by simpa only [Real.norm_eq_abs] using hi.norm)
        ((integrable_heatKernel_exp_abs one_pos (c * sqrt H)).const_mul _)
      intro y
      dsimp only
      rw [abs_mul, abs_of_pos (heatKernel_pos one_pos y)]
      calc
        _ ≤ heatKernel ℝ 1 y * ((M * exp (c * |x|)) * exp (c * sqrt H * |y|)) :=
          mul_le_mul_of_nonneg_left (hbound y) (heatKernel_pos one_pos y).le
        _ = _ := by ring
    _ = _ := by rw [integral_const_mul]; ring

/-- A continuous forcing bounded by `M exp(c|x|)` on a closed strip has a Duhamel
bound linear in elapsed time, with an explicit finite Gaussian exponential moment. -/
theorem abs_heatDuhamel_le {f : ℝ → ℝ → ℝ} {T M c : ℝ}
    (hf : ContinuousOn (Function.uncurry f) (Icc 0 T ×ˢ univ)) (hM : 0 ≤ M) (hc : 0 ≤ c)
    (hb : ∀ s ∈ Icc 0 T, ∀ x, |f s x| ≤ M * exp (c * |x|))
    {ν : ℝ} (hν : 0 ≤ ν) {t : ℝ} (ht : t ∈ Icc 0 T) (x : ℝ) :
    |heatDuhamel ν f t x| ≤ t * M *
      (∫ y : ℝ, heatKernel ℝ 1 y * exp (c * sqrt (ν * T) * |y|)) * exp (c * |x|) := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun s => heatSolution (f s) (ν * (t - s)) x)
    (a := 0) (b := t) (C := M *
      (∫ y : ℝ, heatKernel ℝ 1 y * exp (c * sqrt (ν * T) * |y|)) * exp (c * |x|)) ?_
  · simpa only [Real.norm_eq_abs, sub_zero, abs_of_nonneg ht.1, heatDuhamel,
      mul_assoc, mul_comm, mul_left_comm] using h
  · intro s hs
    have hs₁ : s ∈ Ioc 0 t := by simpa [uIoc_of_le ht.1] using hs
    have hsT : s ∈ Icc 0 T := ⟨hs₁.1.le, hs₁.2.trans ht.2⟩
    have hfs : Continuous (f s) := hf.comp_continuous
      (continuous_const.prodMk continuous_id) (fun y => ⟨hsT, mem_univ y⟩)
    have htime : ν * (t - s) ≤ ν * T :=
      mul_le_mul_of_nonneg_left ((sub_le_self t hs₁.1.le).trans ht.2) hν
    simpa only [Real.norm_eq_abs] using
      abs_heatSolution_le_exp_bound hfs hM hc (hb s hsT) htime x

/-- Duhamel evolution preserves uniform exponential spatial growth on a finite
nonnegative time strip when the viscosity is nonnegative. -/
theorem heatDuhamel_hasExpGrowthOnStrip {f : ℝ → ℝ → ℝ} {T ν : ℝ}
    (hf : ContinuousOn (Function.uncurry f) (Icc 0 T ×ˢ univ))
    (hg : HeatWholeLine.HasExpGrowthOnStrip f T) (hν : 0 ≤ ν) (hT : 0 ≤ T) :
    HeatWholeLine.HasExpGrowthOnStrip (heatDuhamel ν f) T := by
  obtain ⟨M, c, hM, hc, hb⟩ := hg
  let J := ∫ y : ℝ, heatKernel ℝ 1 y * exp (c * sqrt (ν * T) * |y|)
  have hJ : 0 ≤ J := integral_nonneg (fun y =>
    mul_nonneg (heatKernel_pos one_pos y).le (exp_pos _).le)
  refine ⟨T * M * J, c, mul_nonneg (mul_nonneg hT hM) hJ, hc, fun t ht x => ?_⟩
  exact (abs_heatDuhamel_le hf hM hc hb hν ht x).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ht.2 hM) hJ) (exp_pos _).le)

private theorem continuous_slice {f : ℝ → ℝ → ℝ} {T s : ℝ}
    (hf : ContinuousOn (Function.uncurry f) (Icc 0 T ×ˢ univ)) (hs : s ∈ Icc 0 T) :
    Continuous (f s) :=
  hf.comp_continuous (continuous_const.prodMk continuous_id) (fun y => ⟨hs, mem_univ y⟩)

private theorem growth_slice {f : ℝ → ℝ → ℝ} {T s : ℝ}
    (hg : HeatWholeLine.HasExpGrowthOnStrip f T) (hs : s ∈ Icc 0 T) :
    HasExpGrowth (f s) := by
  obtain ⟨M, c, hM, hc, hb⟩ := hg
  exact ⟨M, c, hM, hc, hb s hs⟩

/-- Heat evolution preserves addition for continuous data of exponential growth,
including its stationary extension at nonpositive heat times. -/
theorem heatSolution_add_of_exp_growth {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hbf : HasExpGrowth f) (hbg : HasExpGrowth g) (t x : ℝ) :
    heatSolution (fun y => f y + g y) t x = heatSolution f t x + heatSolution g t x := by
  by_cases ht : 0 < t
  · simp only [heatSolution_of_pos _ ht, mul_add]
    exact integral_add (integrable_heatKernel_mul_of_exp_growth hf.aestronglyMeasurable hbf ht x)
      (integrable_heatKernel_mul_of_exp_growth hg.aestronglyMeasurable hbg ht x)
  · simp only [heatSolution_of_nonpos _ (le_of_not_gt ht)]

/-- Addition of continuous exponentially growing forcing commutes with Duhamel evolution
at each time in the closed strip. No separate integrability assumptions are needed. -/
theorem heatDuhamel_add {f g : ℝ → ℝ → ℝ} {T : ℝ}
    (hf : ContinuousOn (Function.uncurry f) (Icc 0 T ×ˢ univ))
    (hg : ContinuousOn (Function.uncurry g) (Icc 0 T ×ˢ univ))
    (hbf : HeatWholeLine.HasExpGrowthOnStrip f T)
    (hbg : HeatWholeLine.HasExpGrowthOnStrip g T) (ν : ℝ) {t : ℝ}
    (ht : t ∈ Icc 0 T) (x : ℝ) :
    heatDuhamel ν (fun s y => f s y + g s y) t x =
      heatDuhamel ν f t x + heatDuhamel ν g t x := by
  unfold heatDuhamel
  rw [← intervalIntegral.integral_add (intervalIntegrable_heatDuhamel hf hbf ν ht x)
    (intervalIntegrable_heatDuhamel hg hbg ν ht x)]
  apply intervalIntegral.integral_congr
  intro s hs
  have hs₁ : s ∈ Icc 0 t := by simpa [uIcc_of_le ht.1] using hs
  have hsT : s ∈ Icc 0 T := ⟨hs₁.1, hs₁.2.trans ht.2⟩
  exact heatSolution_add_of_exp_growth (continuous_slice hf hsT) (continuous_slice hg hsT)
    (growth_slice hbf hsT) (growth_slice hbg hsT) _ x

/-- Order between continuous exponentially growing forcing terms is preserved on the
closed nonnegative time strip. -/
theorem heatDuhamel_mono {f g : ℝ → ℝ → ℝ} {T : ℝ}
    (hf : ContinuousOn (Function.uncurry f) (Icc 0 T ×ˢ univ))
    (hg : ContinuousOn (Function.uncurry g) (Icc 0 T ×ˢ univ))
    (hbf : HeatWholeLine.HasExpGrowthOnStrip f T)
    (hbg : HeatWholeLine.HasExpGrowthOnStrip g T)
    (hfg : ∀ s ∈ Icc 0 T, ∀ y, f s y ≤ g s y) (ν : ℝ) {t : ℝ}
    (ht : t ∈ Icc 0 T) (x : ℝ) : heatDuhamel ν f t x ≤ heatDuhamel ν g t x := by
  apply intervalIntegral.integral_mono_on ht.1
    (intervalIntegrable_heatDuhamel hf hbf ν ht x)
    (intervalIntegrable_heatDuhamel hg hbg ν ht x)
  intro s hs
  have hsT : s ∈ Icc 0 T := ⟨hs.1, hs.2.trans ht.2⟩
  exact heatSolution_mono_of_exp_growth
    (continuous_slice hf hsT).aestronglyMeasurable (continuous_slice hg hsT).aestronglyMeasurable
    (growth_slice hbf hsT) (growth_slice hbg hsT) (hfg s hsT) _ x

end MathlibExt.Analysis.PDE.HeatKernel
