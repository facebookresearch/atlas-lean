/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.PDE.HeatKernelExponentialGrowth
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.Ring

/-!
# Joint continuity of the heat evolution at initial time

Continuous data of at most exponential growth have jointly continuous heat
convolution, including time zero. The proof uses the fixed time-one Gaussian
rescaling and a locally uniform integrable bound. Spatial derivative commutation
also gives joint continuity of the first spatial derivative for `C¹` data with
exponentially growing derivative.

The all-real-time statements use the existing stationary extension `f x` at
nonpositive times. They assert no backward heat equation, no time derivative at
zero, and no uniform-in-space initial convergence. The Gaussian domination is
that of Gesztesy and Holden, *The Cole–Hopf and Miura transformations revisited*,
Remark 3.5, https://arxiv.org/abs/solv-int/9812025.
-/

@[expose] public section

open MeasureTheory Filter Topology Set Real
open scoped ContDiff
open MathlibExt.Analysis

namespace MathlibExt.Analysis.PDE.HeatKernel

/-- For every `f` and all real `t`, `x`, the heat evolution of `f` is a rescaled Gaussian
integral: `heatSolution f t x = ∫ y, heatKernel ℝ 1 y * f (x - sqrt t * y)`, where
`heatKernel ℝ 1 y = (4 * π) ^ (-1 / 2) * exp (-y ^ 2 / 4)`. For `t ≤ 0`, where `sqrt t = 0`,
both sides equal `f x`. -/
theorem heatSolution_rescaled_all (f : ℝ → ℝ) (t x : ℝ) :
    heatSolution f t x = ∫ y, heatKernel ℝ 1 y * f (x - sqrt t * y) := by
  by_cases ht : 0 < t
  · exact heatSolution_rescaled f ht x
  · rw [heatSolution_of_nonpos f (le_of_not_gt ht), sqrt_eq_zero_of_nonpos (le_of_not_gt ht)]
    simp only [zero_mul, sub_zero, integral_mul_const, integral_heatKernel one_pos, one_mul]

/-- Joint continuity, including time zero, for continuous data of exponential growth. -/
theorem heatSolution_continuous_of_exp_growth {f : ℝ → ℝ} (hf : Continuous f)
    (hg : HasExpGrowth f) : Continuous (Function.uncurry (heatSolution f)) := by
  simp_rw [Function.uncurry_def, heatSolution_rescaled_all]
  apply continuous_iff_continuousAt.mpr
  intro p
  obtain ⟨A, c, _, _, h⟩ := hg.affine_bound (|p.2| + 1) (|sqrt p.1| + 1)
  have hz : ∀ᶠ q : ℝ × ℝ in 𝓝 p, |q.2| < |p.2| + 1 :=
    (continuous_snd.abs.tendsto p).eventually_lt_const (lt_add_one _)
  have hs : ∀ᶠ q : ℝ × ℝ in 𝓝 p, |sqrt q.1| < |sqrt p.1| + 1 :=
    ((continuous_sqrt.comp continuous_fst).abs.tendsto p).eventually_lt_const (lt_add_one _)
  refine tendsto_integral_filter_of_dominated_convergence
    (fun y => (heatKernel ℝ 1 y * exp (c * |y|)) * A) ?_ ?_
    ((integrable_heatKernel_exp_abs one_pos c).mul_const A) ?_
  · filter_upwards with q
    exact ((heatKernel_contDiff 1).continuous.mul
      (hf.comp (continuous_const.sub (continuous_const.mul continuous_id)))).aestronglyMeasurable
  · filter_upwards [hz, hs] with q hqz hqs
    filter_upwards with y
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (heatKernel_pos one_pos y)]
    calc
      _ ≤ heatKernel ℝ 1 y * (A * exp (c * |y|)) :=
        mul_le_mul_of_nonneg_left (h q.2 (sqrt q.1) y hqz.le hqs.le)
          (heatKernel_pos one_pos y).le
      _ = _ := by ring
  · filter_upwards with y
    exact (continuous_const.mul (hf.comp
      (continuous_snd.sub ((continuous_sqrt.comp continuous_fst).mul continuous_const)))).tendsto p

/-- The spatial derivative is jointly continuous up to initial time under exponential growth. -/
theorem heatSolution_deriv_continuous_of_exp_growth {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hg : HasExpGrowth f) (hdg : HasExpGrowth (deriv f)) :
    Continuous (fun p : ℝ × ℝ => deriv (heatSolution f p.1) p.2) := by
  simp_rw [(heatSolution_hasDerivAt_deriv_of_exp_growth hf hg hdg _ _).deriv]
  exact heatSolution_continuous_of_exp_growth hf.continuous_deriv_one hdg

/-- Heat convolution preserves order for exponentially growing measurable data. -/
theorem heatSolution_mono_of_exp_growth {f g : ℝ → ℝ}
    (hf : AEStronglyMeasurable f) (hg : AEStronglyMeasurable g)
    (hbf : HasExpGrowth f) (hbg : HasExpGrowth g) (hfg : ∀ x, f x ≤ g x) (t x : ℝ) :
    heatSolution f t x ≤ heatSolution g t x := by
  by_cases ht : 0 < t
  · rw [heatSolution_of_pos _ ht, heatSolution_of_pos _ ht]
    exact integral_mono (integrable_heatKernel_mul_of_exp_growth hf hbf ht x)
      (integrable_heatKernel_mul_of_exp_growth hg hbg ht x)
      (fun y => mul_le_mul_of_nonneg_left (hfg y) (heatKernel_pos ht (x - y)).le)
  · simpa only [heatSolution_of_nonpos _ (le_of_not_gt ht)] using hfg x

end MathlibExt.Analysis.PDE.HeatKernel
