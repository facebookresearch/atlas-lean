/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.PDE.HeatKernelGradient
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum

open MeasureTheory Set Real
open MathlibExt.Analysis MathlibExt.Analysis.PDE.HeatKernel

-- Cusps in the initial datum do not prevent positive-time differentiation.
example {t : ℝ} (ht : 0 < t) (x : ℝ) :
    deriv (heatSolution (fun y => |sin y|) t) x = -(1 / (2 * sqrt t)) *
      ∫ y, y * heatKernel ℝ 1 y * |sin (x - sqrt t * y)| :=
  heatSolution_deriv_rescaled_of_exp_growth (by fun_prop)
    (HasExpGrowth.of_bounded ⟨1, fun y => by simpa only [abs_abs] using abs_sin_le_one y⟩) ht x

-- A quantitative bound for a nonsmooth datum, with the correct time scale.
example {t H : ℝ} (ht : 0 < t) (hH : t ≤ H) (x : ℝ) :
    |deriv (heatSolution (fun y => |sin y|) t) x| ≤
      (1 / (2 * sqrt t)) * (∫ y : ℝ, |y| * heatKernel ℝ 1 y) := by
  simpa using abs_heatSolution_deriv_le_exp_bound (by fun_prop)
    (M := 1) (c := 0) (by norm_num) (by norm_num)
    (fun y => by simpa only [abs_abs, zero_mul, exp_zero, mul_one] using abs_sin_le_one y) ht hH x

-- The derivative identity works for measurable discontinuous initial data too.
example {t : ℝ} (ht : 0 < t) (x : ℝ) :
    deriv (heatSolution ((Iic (0 : ℝ)).indicator (fun _ => (1 : ℝ))) t) x =
      -(1 / (2 * sqrt t)) * ∫ y : ℝ, y * heatKernel ℝ 1 y *
        (Iic (0 : ℝ)).indicator (fun _ => (1 : ℝ)) (x - sqrt t*y) := by
  apply heatSolution_deriv_rescaled_of_exp_growth
    (measurable_const.indicator measurableSet_Iic).aestronglyMeasurable _ ht x
  apply HasExpGrowth.of_bounded
  refine ⟨1,fun y => ?_⟩
  by_cases hy : y ∈ Iic (0 : ℝ) <;> simp [hy]

-- Gaussian first moments handle noncompact exponential data and negative scales.
example (x : ℝ) :
    Integrable (fun y : ℝ => y * heatKernel ℝ 1 y * exp (x - (-2) * y)) :=
  integrable_heatKernel_firstMoment_affine Real.continuous_exp
    (by simpa using HasExpGrowth.exp_linear 1) x (-2)

example {t : ℝ} (ht : 0 < t) (c : ℝ) :
    Integrable (fun y : ℝ => |y| * heatKernel ℝ t y * exp (c * |y|)) :=
  integrable_heatKernel_abs_mul_exp_abs ht c

example {t H : ℝ} (ht : 0 < t) (hH : t ≤ H) (x : ℝ) :
    |deriv (heatSolution (fun y => exp |y|) t) x| ≤ (1 / (2 * sqrt t)) *
      (∫ y : ℝ, |y| * heatKernel ℝ 1 y * exp (sqrt H * |y|)) * exp |x| := by
  simpa using abs_heatSolution_deriv_le_exp_bound (by fun_prop)
    (M := 1) (c := 1) (by norm_num) (by norm_num)
    (fun y => by simp [abs_of_pos (exp_pos |y|)]) ht hH x

example (x : ℝ) :
    |∫ y : ℝ, y * heatKernel ℝ 1 y * exp (x - (-2) * y)| ≤
      exp |x| * ∫ y : ℝ, |y| * heatKernel ℝ 1 y * exp (2*|y|) := by
  simpa using abs_heatKernel_firstMoment_le_exp_bound Real.continuous_exp
    (M := 1) (c := 1) (by norm_num) (by norm_num)
    (fun y => by simpa only [one_mul,abs_of_pos (exp_pos _)] using
      exp_le_exp.mpr (le_abs_self y)) (s := -2) (S := 2) (by norm_num) x
