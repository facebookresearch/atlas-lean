/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.PDE.HeatKernelBounds
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Heat-kernel initial-value construction in one dimension

The Gaussian convolution of bounded continuous real data has actual first and
second spatial derivatives and an actual time derivative on positive time, and
satisfies the classical heat equation. Its positive-time limit recovers the
initial datum pointwise. The datum itself need not be differentiable or integrable.

We use the existing `heatKernel`; the extension at nonpositive time is the given
datum. This extension is a convention, not a claim to solve a backward heat problem.
No uniqueness or higher/joint boundary regularity is asserted here.

Reference: M. Schmidt, *Partial Differential Equations*, HWS 2025, Chapter 4,
Theorem 4.3, https://www.wim.uni-mannheim.de/media/Lehrstuehle/wim/schmidt/HWS2025/chapter_4.pdf.
The theorem in the reference also asserts joint smoothness, beyond the classical
PDE orders proved below.
-/

@[expose] public section

open MeasureTheory Filter Topology Set Real

namespace MathlibExt.Analysis.PDE.HeatKernel

/-- Heat-kernel convolution at positive time, extended by the initial datum at
nonpositive time. Differential results concern positive time only. -/
noncomputable def heatSolution (f : ℝ → ℝ) (t x : ℝ) : ℝ :=
  if 0 < t then ∫ y, heatKernel ℝ t (x - y) * f y else f x

/-- Positive-time convolution formula. -/
theorem heatSolution_of_pos (f : ℝ → ℝ) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    heatSolution f t x = ∫ y, heatKernel ℝ t (x - y) * f y := by simp [heatSolution, ht]

/-- The chosen extension equals the initial datum at nonpositive times. -/
theorem heatSolution_of_nonpos (f : ℝ → ℝ) {t : ℝ} (ht : t ≤ 0) (x : ℝ) :
    heatSolution f t x = f x := by simp [heatSolution, not_lt.mpr ht]

/-- At time `0` the heat evolution of `f` is `f` itself: `heatSolution f 0 x = f x`. Here
`heatSolution f t` is the convolution of `f` with the heat kernel for `t > 0`, and `f` for
`t ≤ 0`. -/
@[simp] theorem heatSolution_zero (f : ℝ → ℝ) (x : ℝ) : heatSolution f 0 x = f x :=
  heatSolution_of_nonpos f le_rfl x

/-- Bounded continuous data give an integrable convolution integrand. -/
theorem integrable_heatKernel_mul {f : ℝ → ℝ} (hf : Continuous f)
    (hb : ∃ M, ∀ x, |f x| ≤ M) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    Integrable (fun y => heatKernel ℝ t (x - y) * f y) := by
  obtain ⟨M, hM⟩ := hb
  exact ((integrable_heatKernel (E := ℝ) ht).comp_sub_left x).mul_bdd
    hf.aestronglyMeasurable (ae_of_all _ (fun y => by simpa only [Real.norm_eq_abs] using hM y))

private theorem abs_le_of_mem_ball {x z : ℝ} (hz : z ∈ Metric.ball x 1) :
    |z| ≤ |x| + 1 := by
  have hdist : |z - x| < 1 := by simpa only [Metric.mem_ball, Real.dist_eq] using hz
  calc
    |z| = |(z - x) + x| := by congr 1; ring
    _ ≤ |z - x| + |x| := abs_add_le _ _
    _ ≤ _ := by linarith

private theorem mul_bound {k f B : ℝ → ℝ} {M : ℝ} (hM : ∀ y, |f y| ≤ M)
    (hk : ∀ y, ‖k y‖ ≤ B y) (y : ℝ) : ‖k y * f y‖ ≤ B y * M := by
  rw [norm_mul]
  exact mul_le_mul (hk y) (by simpa only [Real.norm_eq_abs] using hM y)
    (norm_nonneg _) ((norm_nonneg _).trans (hk y))

private theorem integral_hasDerivAt_space {f : ℝ → ℝ} (hf : Continuous f)
    (hb : ∃ M, ∀ x, |f x| ≤ M) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    Integrable (fun y => heatKernelDx t (x - y) * f y) ∧
    HasDerivAt (fun z => ∫ y, heatKernel ℝ t (z - y) * f y)
      (∫ y, heatKernelDx t (x - y) * f y) x := by
  obtain ⟨M, hM⟩ := hb
  obtain ⟨B, hi, hB⟩ := exists_integrable_heatKernel_bound (a := t) (b := t)
    (R := |x| + 1) ht le_rfl
  refine hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun z y => heatKernel ℝ t (z - y) * f y)
    (F' := fun z y => heatKernelDx t (z - y) * f y)
    (s := Metric.ball x 1) (bound := fun y => B y * M)
    (Metric.ball_mem_nhds x (by norm_num)) ?_
    (integrable_heatKernel_mul hf ⟨M, hM⟩ ht x) ?_ ?_ (hi.mul_const M) ?_
  · filter_upwards with z
    exact (((heatKernel_contDiff t).continuous.comp (continuous_const.sub continuous_id)).mul
      hf).aestronglyMeasurable
  · exact (((heatKernelDx_continuous t).comp (continuous_const.sub continuous_id)).mul
      hf).aestronglyMeasurable
  · filter_upwards with y z hz
    exact mul_bound hM (fun w => (hB t ⟨le_rfl, le_rfl⟩ z (abs_le_of_mem_ball hz) w).2.1) y
  · filter_upwards with y z _
    simpa using! ((hasDerivAt_heatKernel_space t (z - y)).comp z
      ((hasDerivAt_id' z).sub_const y)).mul_const (f y)

/-- Actual first spatial derivative of the solution. -/
theorem heatSolution_hasDerivAt_space {f : ℝ → ℝ} (hf : Continuous f)
    (hb : ∃ M, ∀ x, |f x| ≤ M) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (heatSolution f t) (∫ y, heatKernelDx t (x - y) * f y) x := by
  have he : heatSolution f t = fun z => ∫ y, heatKernel ℝ t (z - y) * f y :=
    funext (heatSolution_of_pos f ht)
  rw [he]
  exact (integral_hasDerivAt_space hf hb ht x).2

private theorem integral_hasDerivAt_space_two {f : ℝ → ℝ} (hf : Continuous f)
    (hb : ∃ M, ∀ x, |f x| ≤ M) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    Integrable (fun y => heatKernelDxx t (x - y) * f y) ∧
    HasDerivAt (fun z => ∫ y, heatKernelDx t (z - y) * f y)
      (∫ y, heatKernelDxx t (x - y) * f y) x := by
  obtain ⟨M, hM⟩ := hb
  obtain ⟨B, hi, hB⟩ := exists_integrable_heatKernel_bound (a := t) (b := t)
    (R := |x| + 1) ht le_rfl
  refine hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun z y => heatKernelDx t (z - y) * f y)
    (F' := fun z y => heatKernelDxx t (z - y) * f y)
    (s := Metric.ball x 1) (bound := fun y => B y * M)
    (Metric.ball_mem_nhds x (by norm_num)) ?_
    (integral_hasDerivAt_space hf ⟨M, hM⟩ ht x).1 ?_ ?_ (hi.mul_const M) ?_
  · filter_upwards with z
    exact (((heatKernelDx_continuous t).comp (continuous_const.sub continuous_id)).mul
      hf).aestronglyMeasurable
  · exact (((heatKernelDxx_continuous t).comp (continuous_const.sub continuous_id)).mul
      hf).aestronglyMeasurable
  · filter_upwards with y z hz
    exact mul_bound hM (fun w => (hB t ⟨le_rfl, le_rfl⟩ z (abs_le_of_mem_ball hz) w).2.2) y
  · filter_upwards with y z _
    simpa using! ((hasDerivAt_heatKernelDx_space ht (z - y)).comp z
      ((hasDerivAt_id' z).sub_const y)).mul_const (f y)

/-- Actual second spatial derivative; existence of the first derivative is proved
separately by `heatSolution_hasDerivAt_space`. -/
theorem heatSolution_hasDerivAt_space_two {f : ℝ → ℝ} (hf : Continuous f)
    (hb : ∃ M, ∀ x, |f x| ≤ M) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (deriv (heatSolution f t)) (∫ y, heatKernelDxx t (x - y) * f y) x := by
  have he : deriv (heatSolution f t) = fun z => ∫ y, heatKernelDx t (z - y) * f y :=
    funext (fun z => (heatSolution_hasDerivAt_space hf hb ht z).deriv)
  rw [he]
  exact (integral_hasDerivAt_space_two hf hb ht x).2

private theorem integral_hasDerivAt_time {f : ℝ → ℝ} (hf : Continuous f)
    (hb : ∃ M, ∀ x, |f x| ≤ M) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (fun s => ∫ y, heatKernel ℝ s (x - y) * f y)
      (∫ y, heatKernelDxx t (x - y) * f y) t := by
  obtain ⟨M, hM⟩ := hb
  obtain ⟨B, hi, hB⟩ := exists_integrable_heatKernel_bound
    (a := t / 2) (b := 2 * t) (R := |x|) (by positivity) (by linarith)
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun s y => heatKernel ℝ s (x - y) * f y)
    (F' := fun s y => heatKernelDxx s (x - y) * f y)
    (s := Ioo (t / 2) (2 * t)) (bound := fun y => B y * M)
    (Ioo_mem_nhds (by linarith : t / 2 < t) (by linarith : t < 2 * t)) ?_
    (integrable_heatKernel_mul hf ⟨M, hM⟩ ht x) ?_ ?_ (hi.mul_const M) ?_).2
  · filter_upwards with s
    exact (((heatKernel_contDiff s).continuous.comp (continuous_const.sub continuous_id)).mul
      hf).aestronglyMeasurable
  · exact (((heatKernelDxx_continuous t).comp (continuous_const.sub continuous_id)).mul
      hf).aestronglyMeasurable
  · filter_upwards with y s hs
    exact mul_bound hM (fun w => (hB s ⟨hs.1.le, hs.2.le⟩ x le_rfl w).2.2) y
  · filter_upwards with y s hs
    have hs0 : 0 < s := lt_trans (by positivity : 0 < t / 2) hs.1
    exact (hasDerivAt_heatKernel_time_dxx hs0 (x - y)).mul_const (f y)

/-- Classical heat equation for bounded continuous data: the actual time derivative
is the actual second spatial derivative at every positive-time point. -/
theorem heatSolution_hasDerivAt_time {f : ℝ → ℝ} (hf : Continuous f)
    (hb : ∃ M, ∀ x, |f x| ≤ M) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (fun s => heatSolution f s x) (deriv (deriv (heatSolution f t)) x) t := by
  rw [(heatSolution_hasDerivAt_space_two hf hb ht x).deriv]
  apply (integral_hasDerivAt_time hf hb ht x).congr_of_eventuallyEq
  filter_upwards [isOpen_Ioi.mem_nhds ht] with s hs
  exact heatSolution_of_pos f hs x

/-- Rescaling space by `√t` converts the positive-time kernel to the time-one kernel. -/
theorem heatKernel_sqrt_time {t : ℝ} (ht : 0 < t) (y : ℝ) :
    heatKernel ℝ t (sqrt t * y) = (sqrt t)⁻¹ * heatKernel ℝ 1 y := by
  rw [heatKernel_real, heatKernel_real, mul_pow, sq_sqrt ht.le]
  have hc : (4 * π * t) ^ (-(1 : ℝ) / 2) =
      (sqrt t)⁻¹ * (4 * π) ^ (-(1 : ℝ) / 2) := by
    rw [mul_rpow (by positivity) ht.le]
    have he : t ^ (-(1 : ℝ) / 2) = (sqrt t)⁻¹ := by
      rw [neg_div, rpow_neg ht.le, ← sqrt_eq_rpow]
    rw [he]
    ring
  rw [hc]
  have he : -(t * y ^ 2) / (4 * t) = -y ^ 2 / 4 := by field_simp
  rw [he]
  simp only [mul_one]
  ring

/-- A change of variables expresses the solution using a fixed integrable Gaussian. -/
theorem heatSolution_rescaled (f : ℝ → ℝ) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    heatSolution f t x = ∫ y, heatKernel ℝ 1 y * f (x - sqrt t * y) := by
  rw [heatSolution_of_pos f ht]
  have hshift : (∫ y, heatKernel ℝ t (x - y) * f y) =
      ∫ y, heatKernel ℝ t y * f (x - y) := by
    have h := integral_sub_left_eq_self
      (fun y => heatKernel ℝ t y * f (x - y)) volume x
    simpa only [sub_sub_cancel] using h
  rw [hshift]
  have hr := Measure.integral_comp_mul_left
    (fun y => heatKernel ℝ t y * f (x - y)) (sqrt t)
  have hs : 0 < sqrt t := sqrt_pos.mpr ht
  simp only [abs_of_pos (inv_pos.mpr hs), smul_eq_mul] at hr
  have he : (fun y => heatKernel ℝ t (sqrt t * y) * f (x - sqrt t * y)) =
      fun y => (sqrt t)⁻¹ * (heatKernel ℝ 1 y * f (x - sqrt t * y)) := by
    funext y
    rw [heatKernel_sqrt_time ht]
    ring
  rw [he, integral_const_mul] at hr
  exact (mul_left_cancel₀ (inv_ne_zero hs.ne') hr).symm

/-- The positive-time initial trace of the heat solution recovers each value of
bounded continuous initial data. No differentiability or uniform continuity is required. -/
theorem heatSolution_tendsto_zero {f : ℝ → ℝ} (hf : Continuous f)
    (hb : ∃ M, ∀ x, |f x| ≤ M) (x : ℝ) :
    Tendsto (fun t => heatSolution f t x) (𝓝[>] 0) (𝓝 (f x)) := by
  obtain ⟨M, hM⟩ := hb
  have hlim : Tendsto (fun t : ℝ => ∫ y, heatKernel ℝ 1 y * f (x - sqrt t * y))
      (𝓝 0) (𝓝 (∫ y, heatKernel ℝ 1 y * f x)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun y => heatKernel ℝ 1 y * M) ?_ ?_
      ((integrable_heatKernel (E := ℝ) one_pos).mul_const M) ?_
    · filter_upwards with t
      exact ((heatKernel_contDiff 1).continuous.mul
        (hf.comp (continuous_const.sub (continuous_const.mul continuous_id)))).aestronglyMeasurable
    · filter_upwards with t
      filter_upwards with y
      rw [norm_mul, Real.norm_eq_abs (heatKernel ℝ 1 y), abs_of_pos (heatKernel_pos one_pos y)]
      exact mul_le_mul_of_nonneg_left (by simpa only [Real.norm_eq_abs] using hM (x - sqrt t * y))
        (heatKernel_pos one_pos y).le
    · filter_upwards with y
      have hc : ContinuousAt (fun t : ℝ => heatKernel ℝ 1 y * f (x - sqrt t * y)) 0 :=
        continuousAt_const.mul (hf.continuousAt.comp
          (continuousAt_const.sub (continuous_sqrt.continuousAt.mul continuousAt_const)))
      simpa only [sqrt_zero, zero_mul, sub_zero] using hc.tendsto
  rw [integral_mul_const, integral_heatKernel one_pos, one_mul] at hlim
  have he : (fun t => heatSolution f t x) =ᶠ[𝓝[>] 0]
      (fun t => ∫ y, heatKernel ℝ 1 y * f (x - sqrt t * y)) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact heatSolution_rescaled f ht x
  exact (tendsto_congr' he).2 (hlim.mono_left inf_le_left)

/-- Classical PDE and initial trace, with explicit witnesses for both spatial derivatives. -/
theorem heatSolution_solves_initial_value {f : ℝ → ℝ} (hf : Continuous f)
    (hb : ∃ M, ∀ x, |f x| ≤ M) :
    (∀ t : ℝ, 0 < t → ∀ x : ℝ, ∃ ux : ℝ → ℝ, ∃ uxx : ℝ,
      (∀ y : ℝ, HasDerivAt (heatSolution f t) (ux y) y) ∧
      HasDerivAt ux uxx x ∧ HasDerivAt (fun s => heatSolution f s x) uxx t) ∧
    (∀ x : ℝ, Tendsto (fun t => heatSolution f t x) (𝓝[>] 0) (𝓝 (f x))) := by
  refine ⟨?_, heatSolution_tendsto_zero hf hb⟩
  intro t ht x
  refine ⟨deriv (heatSolution f t), deriv (deriv (heatSolution f t)) x, ?_, ?_,
    heatSolution_hasDerivAt_time hf hb ht x⟩
  · intro y
    exact (heatSolution_hasDerivAt_space hf hb ht y).differentiableAt.hasDerivAt
  · exact (heatSolution_hasDerivAt_space_two hf hb ht x).differentiableAt.hasDerivAt

/-- Constant initial data are preserved at all times, including the chosen extension. -/
@[simp] theorem heatSolution_const (c t x : ℝ) : heatSolution (fun _ => c) t x = c := by
  by_cases ht : 0 < t
  · rw [heatSolution_of_pos _ ht, integral_mul_const,
      integral_sub_left_eq_self (heatKernel ℝ t) volume x, integral_heatKernel ht, one_mul]
  · exact heatSolution_of_nonpos _ (le_of_not_gt ht) x

/-- The heat evolution preserves pointwise order for bounded continuous data. -/
theorem heatSolution_mono {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hbf : ∃ M, ∀ x, |f x| ≤ M) (hbg : ∃ M, ∀ x, |g x| ≤ M)
    (hfg : ∀ x, f x ≤ g x) (t x : ℝ) : heatSolution f t x ≤ heatSolution g t x := by
  by_cases ht : 0 < t
  · rw [heatSolution_of_pos _ ht, heatSolution_of_pos _ ht]
    exact integral_mono (integrable_heatKernel_mul hf hbf ht x)
      (integrable_heatKernel_mul hg hbg ht x)
      (fun y => mul_le_mul_of_nonneg_left (hfg y) (heatKernel_pos ht (x - y)).le)
  · simpa only [heatSolution_of_nonpos _ (le_of_not_gt ht)] using hfg x

/-- The original uniform bound is preserved. -/
theorem abs_heatSolution_le {f : ℝ → ℝ} (hf : Continuous f) {M : ℝ}
    (hb : ∀ x, |f x| ≤ M) (t x : ℝ) : |heatSolution f t x| ≤ M := by
  have hM : 0 ≤ M := (abs_nonneg (f 0)).trans (hb 0)
  apply abs_le.mpr
  constructor
  · have h := heatSolution_mono continuous_const hf
      ⟨M, fun _ => by simp only [abs_neg, abs_of_nonneg hM, le_refl]⟩ ⟨M, hb⟩
      (fun y => (abs_le.mp (hb y)).1) t x
    simpa only [heatSolution_const] using h
  · have h := heatSolution_mono hf continuous_const ⟨M, hb⟩
      ⟨M, fun _ => by simp only [abs_of_nonneg hM, le_refl]⟩
      (fun y => (abs_le.mp (hb y)).2) t x
    simpa only [heatSolution_const] using h

/-- Nonnegative data give a nonnegative heat solution. -/
theorem heatSolution_nonneg {f : ℝ → ℝ} (hp : ∀ x, 0 ≤ f x) (t x : ℝ) :
    0 ≤ heatSolution f t x := by
  by_cases ht : 0 < t
  · rw [heatSolution_of_pos _ ht]
    exact integral_nonneg (fun y => mul_nonneg (heatKernel_pos ht (x - y)).le (hp y))
  · simpa only [heatSolution_of_nonpos _ (le_of_not_gt ht)] using hp x

/-- Strictly positive bounded continuous initial data remain strictly positive. -/
theorem heatSolution_pos {f : ℝ → ℝ} (hf : Continuous f)
    (hb : ∃ M, ∀ x, |f x| ≤ M) (hp : ∀ x, 0 < f x) (t x : ℝ) :
    0 < heatSolution f t x := by
  by_cases ht : 0 < t
  · rw [heatSolution_of_pos _ ht]
    have hpos (y : ℝ) : 0 < heatKernel ℝ t (x - y) * f y :=
      mul_pos (heatKernel_pos ht _) (hp y)
    rw [integral_pos_iff_support_of_nonneg (fun y => (hpos y).le)
      (integrable_heatKernel_mul hf hb ht x)]
    have hs : Function.support (fun y => heatKernel ℝ t (x - y) * f y) = univ :=
      eq_univ_of_forall (fun y => ne_of_gt (hpos y))
    rw [hs]
    simp
  · simpa only [heatSolution_of_nonpos _ (le_of_not_gt ht)] using hp x

/-- Linearity in the initial datum. -/
theorem heatSolution_add {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hbf : ∃ M, ∀ x, |f x| ≤ M) (hbg : ∃ M, ∀ x, |g x| ≤ M) (t x : ℝ) :
    heatSolution (fun y => f y + g y) t x = heatSolution f t x + heatSolution g t x := by
  by_cases ht : 0 < t
  · simp only [heatSolution_of_pos _ ht, mul_add]
    exact integral_add (integrable_heatKernel_mul hf hbf ht x)
      (integrable_heatKernel_mul hg hbg ht x)
  · simp only [heatSolution_of_nonpos _ (le_of_not_gt ht)]

/-- Constant scalar multiplication commutes with the heat construction. -/
theorem heatSolution_const_mul (c : ℝ) (f : ℝ → ℝ) (t x : ℝ) :
    heatSolution (fun y => c * f y) t x = c * heatSolution f t x := by
  by_cases ht : 0 < t
  · rw [heatSolution_of_pos _ ht, heatSolution_of_pos _ ht, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with y
    ring
  · simp only [heatSolution_of_nonpos _ (le_of_not_gt ht)]

/-- Positive diffusivity is obtained by scaling time; the resulting actual time
derivative is `ν` times the second spatial derivative. -/
theorem heatSolution_hasDerivAt_time_scaled {f : ℝ → ℝ} (hf : Continuous f)
    (hb : ∃ M, ∀ x, |f x| ≤ M) {ν t : ℝ} (hν : 0 < ν) (ht : 0 < t) (x : ℝ) :
    HasDerivAt (fun s => heatSolution f (ν * s) x)
      (ν * deriv (deriv (heatSolution f (ν * t))) x) t := by
  simpa only [Function.comp_def, mul_one, mul_comm] using!
    (heatSolution_hasDerivAt_time hf hb (mul_pos hν ht) x).comp t
    ((hasDerivAt_id' t).const_mul ν)

/-- Positive time scaling preserves the initial trace. -/
theorem heatSolution_tendsto_zero_scaled {f : ℝ → ℝ} (hf : Continuous f)
    (hb : ∃ M, ∀ x, |f x| ≤ M) {ν : ℝ} (hν : 0 < ν) (x : ℝ) :
    Tendsto (fun t => heatSolution f (ν * t) x) (𝓝[>] 0) (𝓝 (f x)) := by
  have h : Tendsto (fun t : ℝ => ν * t) (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hc : ContinuousAt (fun t : ℝ => ν * t) 0 :=
        continuousAt_const.mul continuousAt_id
      simpa only [mul_zero] using! hc.tendsto.mono_left (inf_le_left : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact mul_pos hν ht
  exact (heatSolution_tendsto_zero hf hb x).comp h

end MathlibExt.Analysis.PDE.HeatKernel
