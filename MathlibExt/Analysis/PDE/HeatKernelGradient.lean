/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.PDE.HeatKernelExponentialGrowth
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Weighted first derivatives of Gaussian heat evolution

Differentiating the Gaussian and rescaling to time one gives an integrable
first moment, with a time factor of order `t⁻¹ᐟ²`. Exponential weights are
absorbed by Gaussian decay. The datum need not have a spatial derivative.

The Gaussian differentiation argument is described in James Nolen,
*Partial Differential Equations and Diffusion Processes*, §2.3, pp. 16–17,
https://math.stanford.edu/~ryzhik/STANFORD/STANF227-10/notes227-09.pdf.
The explicit weighted first-moment estimates below follow by rescaling and
the exponential Gaussian domination proved in `GaussianGrowth`.
-/

@[expose] public section

open MeasureTheory Real Set Filter Topology
open MathlibExt.Analysis MathlibExt.Analysis.GaussianMoments

namespace MathlibExt.Analysis.PDE.HeatKernel

private theorem growth_mul_id {f : ℝ → ℝ} (hg : HasExpGrowth f) :
    HasExpGrowth (fun y => y * f y) := by
  obtain ⟨M, c, hM, hc, hb⟩ := hg
  refine ⟨M,c+1,hM,by linarith,fun y => ?_⟩
  rw [abs_mul]
  calc
    |y| * |f y| ≤ exp |y| * (M * exp (c * |y|)) :=
      mul_le_mul ((le_add_of_nonneg_right zero_le_one).trans (add_one_le_exp _))
        (hb y) (abs_nonneg _) (exp_pos _).le
    _ = M * exp ((c+1)*|y|) := by rw [add_mul, one_mul, exp_add]; ring

private theorem centered_deriv {f : ℝ → ℝ} (hf : AEStronglyMeasurable f) (hg : HasExpGrowth f)
    {t : ℝ} (ht : 0 < t) (x : ℝ) :
    deriv (heatSolution f t) x = ∫ y, -(x-y)/(2 * t) * heatKernel ℝ t (x-y) * f y := by
  have h0 := integrable_heatKernel_mul_of_exp_growth hf hg ht x
  have hf1 : AEStronglyMeasurable (fun y => y * f y) := by
    simpa only [Pi.mul_apply, id_eq] using! continuous_id.aestronglyMeasurable.mul hf
  have h1 := integrable_heatKernel_mul_of_exp_growth hf1 (growth_mul_id hg) ht x
  have he1 : heatKernel ℝ t x * gaussianMoment f 1 (1/(4*t),x/(2 * t)) =
      ∫ y, heatKernel ℝ t (x-y) * (y * f y) := by
    have hh := heatSolution_eq_gaussianMoment (fun y => y * f y) ht x
    have he : gaussianMoment (fun y => y * f y) 0 (1/(4*t),x/(2 * t)) =
        gaussianMoment f 1 (1/(4*t),x/(2 * t)) := by
      unfold gaussianMoment
      apply integral_congr_ae
      filter_upwards with y
      simp only [pow_zero, one_mul, pow_one]
      ring
    rw [he, heatSolution_of_pos _ ht] at hh
    simpa only [heatKernel_real] using hh.symm
  rw [(heatSolution_hasDerivAt_space_of_exp_growth hf hg ht x).deriv, he1,
    heatSolution_of_pos _ ht, ← integral_const_mul, ← integral_div,
    ← integral_add (h0.const_mul _) (h1.div_const _)]
  apply integral_congr_ae
  filter_upwards with y
  ring

/-- The actual spatial derivative uses a fixed Gaussian and a `t⁻¹ᐟ²` time factor. -/
theorem heatSolution_deriv_rescaled_of_exp_growth {f : ℝ → ℝ}
    (hf : AEStronglyMeasurable f) (hg : HasExpGrowth f)
    {t : ℝ} (ht : 0 < t) (x : ℝ) :
    deriv (heatSolution f t) x = -(1 / (2 * sqrt t)) *
      ∫ y, y * heatKernel ℝ 1 y * f (x - sqrt t * y) := by
  rw [centered_deriv hf hg ht x]
  have hshift : (∫ y, -(x-y)/(2 * t) * heatKernel ℝ t (x-y) * f y) =
      ∫ y, -y/(2 * t) * heatKernel ℝ t y * f (x-y) := by
    have h := integral_sub_left_eq_self
      (fun y => -y/(2 * t) * heatKernel ℝ t y * f (x-y)) volume x
    simpa only [sub_sub_cancel] using h
  rw [hshift]
  have hr := Measure.integral_comp_mul_left
    (fun y => -y/(2 * t) * heatKernel ℝ t y * f (x-y)) (sqrt t)
  have hs : 0 < sqrt t := sqrt_pos.mpr ht
  simp only [abs_of_pos (inv_pos.mpr hs), smul_eq_mul] at hr
  have he : (fun y => -(sqrt t*y)/(2 * t) * heatKernel ℝ t (sqrt t*y) * f (x-sqrt t*y)) =
      fun y => (sqrt t)⁻¹ * (-(1 / (2 * sqrt t)) * (y * heatKernel ℝ 1 y * f (x-sqrt t*y))) := by
    funext y
    rw [heatKernel_sqrt_time ht]
    field_simp
    ring_nf
    rw [sq_sqrt ht.le]
    ring
  rw [he, integral_const_mul, integral_const_mul] at hr
  exact (mul_left_cancel₀ (inv_ne_zero hs.ne') hr).symm

/-- The first absolute Gaussian moment absorbs any linear exponential weight. -/
theorem integrable_heatKernel_abs_mul_exp_abs {t : ℝ} (ht : 0 < t) (c : ℝ) :
    Integrable (fun y : ℝ => |y| * heatKernel ℝ t y * exp (c * |y|)) := by
  have hi := (integrable_pow_mul_exp_neg_sq_add_abs
    (by positivity : 0 < 1 / (4 * t)) c 1).const_mul ((4 * π * t) ^ (-(1 : ℝ) / 2))
  convert hi using 1
  funext y
  simp only [pow_one, heatKernel_real, exp_add]
  have he : -y ^ 2 / (4 * t) = -(1 / (4 * t)) * y ^ 2 := by ring
  rw [he]
  ring

/-- A first Gaussian moment remains integrable after affine rescaling of continuous
exponentially growing data. -/
theorem integrable_heatKernel_firstMoment_affine {f : ℝ → ℝ} (hf : Continuous f)
    (hg : HasExpGrowth f) (z s : ℝ) :
    Integrable (fun y => y * heatKernel ℝ 1 y * f (z - s * y)) := by
  obtain ⟨A, c, _, _, h⟩ := hg.affine_bound |z| |s|
  apply ((integrable_heatKernel_abs_mul_exp_abs one_pos c).mul_const A).mono'
    ((continuous_id.mul (heatKernel_contDiff 1).continuous).mul
      (hf.comp (continuous_const.sub (continuous_const.mul continuous_id)))).aestronglyMeasurable
  filter_upwards with y
  change ‖y * heatKernel ℝ 1 y * f (z - s * y)‖ ≤ _
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (heatKernel_pos one_pos y)]
  calc
    _ ≤ |y| * heatKernel ℝ 1 y * (A * exp (c * |y|)) :=
      mul_le_mul_of_nonneg_left (h z s y le_rfl le_rfl)
        (mul_nonneg (abs_nonneg y) (heatKernel_pos one_pos y).le)
    _ = _ := by ring

/-- An explicit weighted first moment bounds affine rescaling of exponentially
bounded data. The scale may have either sign. -/
theorem abs_heatKernel_firstMoment_le_exp_bound {f : ℝ → ℝ} (hf : Continuous f)
    {M c : ℝ} (hM : 0 ≤ M) (hc : 0 ≤ c) (hb : ∀ x, |f x| ≤ M * exp (c * |x|))
    {s S : ℝ} (hsq : |s| ≤ S) (x : ℝ) :
    |∫ y, y * heatKernel ℝ 1 y * f (x - s * y)| ≤ (M * exp (c * |x|)) *
      ∫ y : ℝ, |y| * heatKernel ℝ 1 y * exp (c * S * |y|) := by
  have hbound (y : ℝ) : |f (x - s * y)| ≤
      (M * exp (c * |x|)) * exp (c * S * |y|) := by
    have ha : |x - s * y| ≤ |x| + S * |y| :=
      (abs_sub _ _).trans (add_le_add le_rfl
        (by simpa only [abs_mul] using mul_le_mul_of_nonneg_right hsq (abs_nonneg y)))
    calc
      _ ≤ M * exp (c * |x - s * y|) := hb _
      _ ≤ M * exp (c * (|x| + S * |y|)) :=
        mul_le_mul_of_nonneg_left (exp_le_exp.mpr (mul_le_mul_of_nonneg_left ha hc)) hM
      _ = _ := by simp only [mul_add, exp_add, mul_assoc]
  have hi := integrable_heatKernel_firstMoment_affine hf ⟨M, c, hM, hc, hb⟩ x (s)
  have hI : |∫ y, y * heatKernel ℝ 1 y * f (x - s * y)| ≤
      (M * exp (c * |x|)) *
        ∫ y : ℝ, |y| * heatKernel ℝ 1 y * exp (c * S * |y|) := by
    calc
      _ ≤ ∫ y, |y * heatKernel ℝ 1 y * f (x - s * y)| :=
        MeasureTheory.abs_integral_le_integral_abs
      _ ≤ ∫ y, (M * exp (c * |x|)) *
          (|y| * heatKernel ℝ 1 y * exp (c * S * |y|)) := by
        apply integral_mono (by simpa only [Real.norm_eq_abs] using hi.norm)
          ((integrable_heatKernel_abs_mul_exp_abs one_pos (c * S)).const_mul _)
        intro y
        dsimp only
        rw [abs_mul, abs_mul, abs_of_pos (heatKernel_pos one_pos y)]
        calc
          _ ≤ |y| * heatKernel ℝ 1 y *
              ((M * exp (c * |x|)) * exp (c * S * |y|)) :=
            mul_le_mul_of_nonneg_left (hbound y)
              (mul_nonneg (abs_nonneg y) (heatKernel_pos one_pos y).le)
          _ = _ := by ring
      _ = _ := integral_const_mul _ _
  exact hI

/-- A weighted Gaussian first moment controls the spatial heat derivative uniformly
for `0 < t ≤ H`, without any derivative assumption on the initial datum. -/
theorem abs_heatSolution_deriv_le_exp_bound {f : ℝ → ℝ} (hf : Continuous f)
    {M c : ℝ} (hM : 0 ≤ M) (hc : 0 ≤ c) (hb : ∀ x, |f x| ≤ M * exp (c * |x|))
    {t H : ℝ} (ht : 0 < t) (hH : t ≤ H) (x : ℝ) :
    |deriv (heatSolution f t) x| ≤ (M / (2 * sqrt t)) *
      (∫ y : ℝ, |y| * heatKernel ℝ 1 y * exp (c * sqrt H * |y|)) * exp (c * |x|) := by
  have hI := abs_heatKernel_firstMoment_le_exp_bound hf hM hc hb
    (s := sqrt t) (S := sqrt H)
    (by rw [abs_of_nonneg (sqrt_nonneg _)]; exact sqrt_le_sqrt hH) x
  rw [heatSolution_deriv_rescaled_of_exp_growth hf.aestronglyMeasurable ⟨M, c, hM, hc, hb⟩ ht x,
    abs_mul, abs_neg, abs_of_nonneg (by positivity : 0 ≤ 1 / (2 * sqrt t))]
  calc
    _ ≤ (1 / (2 * sqrt t)) * ((M * exp (c * |x|)) *
        ∫ y : ℝ, |y| * heatKernel ℝ 1 y * exp (c * sqrt H * |y|)) :=
      mul_le_mul_of_nonneg_left hI (by positivity)
    _ = _ := by ring

end MathlibExt.Analysis.PDE.HeatKernel
