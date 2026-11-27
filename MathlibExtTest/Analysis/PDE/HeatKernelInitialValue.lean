/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.PDE.HeatKernelInitialValue
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

open MeasureTheory Filter Topology Set
open MathlibExt.Analysis.PDE.HeatKernel

-- Bounded continuous data need not be integrable or differentiable.
example (f : ℝ → ℝ) (hc : Continuous f) (hb : ∃ M, ∀ x, |f x| ≤ M)
    (t x : ℝ) (ht : 0 < t) :
    HasDerivAt (fun s => heatSolution f s x) (deriv (deriv (heatSolution f t)) x) t :=
  heatSolution_hasDerivAt_time hc hb ht x

example (f : ℝ → ℝ) (hc : Continuous f) (hb : ∃ M, ∀ x, |f x| ≤ M) (x : ℝ) :
    Tendsto (fun t => heatSolution f t x) (𝓝[>] 0) (𝓝 (f x)) :=
  heatSolution_tendsto_zero hc hb x

private noncomputable def cappedAbs (x : ℝ) : ℝ := min 1 |x|

private theorem cappedAbs_continuous : Continuous cappedAbs :=
  continuous_const.min continuous_abs

private theorem cappedAbs_bound (x : ℝ) : |cappedAbs x| ≤ 1 := by
  change |min 1 (|x|)| ≤ 1
  rw [abs_of_nonneg (le_min (by norm_num) (abs_nonneg x))]
  exact min_le_left _ _

-- A bounded datum with a corner: no derivative premise is supplied.
example (t x : ℝ) (ht : 0 < t) :
    HasDerivAt (fun s => heatSolution cappedAbs s x)
      (deriv (deriv (heatSolution cappedAbs t)) x) t :=
  heatSolution_hasDerivAt_time cappedAbs_continuous ⟨1, cappedAbs_bound⟩ ht x

-- Derivative existence in space is checked independently of the PDE equality.
example : DifferentiableAt ℝ (heatSolution cappedAbs 1) 0 ∧
    DifferentiableAt ℝ (deriv (heatSolution cappedAbs 1)) 0 :=
  ⟨(heatSolution_hasDerivAt_space cappedAbs_continuous ⟨1, cappedAbs_bound⟩ one_pos 0).differentiableAt,
    (heatSolution_hasDerivAt_space_two cappedAbs_continuous ⟨1, cappedAbs_bound⟩
      one_pos 0).differentiableAt⟩

example : Tendsto (fun t => heatSolution cappedAbs t 0) (𝓝[>] 0) (𝓝 0) := by
  simpa [cappedAbs] using heatSolution_tendsto_zero cappedAbs_continuous ⟨1, cappedAbs_bound⟩ 0

-- Nonintegrable constant data are accepted and preserved, for either sign.
example (t x : ℝ) : heatSolution (fun _ => (-3 : ℝ)) t x = -3 := heatSolution_const _ _ _

example (t x : ℝ) : heatSolution (fun _ => (2 : ℝ)) t x = 2 := heatSolution_const _ _ _

example : ¬ Integrable (fun _ : ℝ => (2 : ℝ)) := by
  simp [integrable_const_iff, isFiniteMeasure_iff]

-- Positive time is essential to the smoothing theorem; the extension keeps the corner.
example (x : ℝ) : heatSolution cappedAbs 0 x = cappedAbs x := heatSolution_zero _ _

example (x : ℝ) : heatSolution cappedAbs (-1) x = cappedAbs x :=
  heatSolution_of_nonpos _ (by norm_num) _

example (t x : ℝ) : |heatSolution cappedAbs t x| ≤ 1 :=
  abs_heatSolution_le cappedAbs_continuous cappedAbs_bound t x

example (t x : ℝ) : 0 ≤ heatSolution cappedAbs t x :=
  heatSolution_nonneg (fun y => le_min (by norm_num) (abs_nonneg y)) t x

-- Adding a positive floor preserves positivity without any initial smoothness assumption.
example (t x : ℝ) : 0 < heatSolution (fun y => 1 + cappedAbs y) t x := by
  apply heatSolution_pos (f := fun y => 1 + cappedAbs y)
    (continuous_const.add cappedAbs_continuous) ?_ ?_ t x
  · refine ⟨2, fun y => ?_⟩
    have h0 : 0 ≤ cappedAbs y := le_min (by norm_num) (abs_nonneg y)
    have h1 := cappedAbs_bound y
    rw [abs_of_nonneg (by linarith)]
    have h2 := le_abs_self (cappedAbs y)
    linarith
  · intro y
    have h0 : 0 ≤ cappedAbs y := le_min (by norm_num) (abs_nonneg y)
    linarith

-- Positive diffusivity changes the PDE coefficient but not the initial values.
example (t x : ℝ) (ht : 0 < t) :
    HasDerivAt (fun s => heatSolution cappedAbs (3 * s) x)
      (3 * deriv (deriv (heatSolution cappedAbs (3 * t))) x) t :=
  heatSolution_hasDerivAt_time_scaled cappedAbs_continuous ⟨1, cappedAbs_bound⟩ (by norm_num) ht x

example (x : ℝ) : Tendsto (fun t => heatSolution cappedAbs (3 * t) x)
    (𝓝[>] 0) (𝓝 (cappedAbs x)) :=
  heatSolution_tendsto_zero_scaled cappedAbs_continuous ⟨1, cappedAbs_bound⟩ (by norm_num) x

-- Scalar linearity and addition use the actual convolution definition.
example (t x : ℝ) : heatSolution (fun y => -2 * cappedAbs y) t x =
    -2 * heatSolution cappedAbs t x := heatSolution_const_mul _ _ _ _

example (t x : ℝ) : heatSolution (fun y => cappedAbs y + 4) t x =
    heatSolution cappedAbs t x + 4 := by
  simpa only [heatSolution_const] using heatSolution_add cappedAbs_continuous continuous_const
    ⟨1, cappedAbs_bound⟩ ⟨4, fun _ => by norm_num⟩ t x

-- The rescaling formula is valid before any regularity hypotheses on the datum.
example (f : ℝ → ℝ) (x : ℝ) : heatSolution f 4 x =
    ∫ y, heatKernel ℝ 1 y * f (x - 2 * y) := by
  have hs : Real.sqrt (4 : ℝ) = 2 := by
    rw [Real.sqrt_eq_iff_mul_self_eq (by norm_num) (by norm_num)]
    norm_num
  simpa only [hs] using heatSolution_rescaled f (by norm_num : (0 : ℝ) < 4) x

private theorem cappedAbs_not_differentiable : ¬ DifferentiableAt ℝ cappedAbs 0 := by
  have he : cappedAbs =ᶠ[𝓝 (0 : ℝ)] (abs : ℝ → ℝ) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1)] with y hy
    have hy' : |y| < 1 := by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hy
    exact min_eq_right hy'.le
  intro hd
  exact not_differentiableAt_abs_zero (hd.congr_of_eventuallyEq he.symm)

-- This is genuine smoothing, not smooth initial data hidden in the hypotheses.
example : ¬ DifferentiableAt ℝ (heatSolution cappedAbs 0) 0 := by
  have he : heatSolution cappedAbs 0 = cappedAbs := funext (heatSolution_zero cappedAbs)
  rw [he]
  exact cappedAbs_not_differentiable
