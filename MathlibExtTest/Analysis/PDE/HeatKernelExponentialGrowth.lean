/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.PDE.HeatKernelExponentialGrowth
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum

open MeasureTheory Filter Topology Set Real
open scoped ContDiff
open MathlibExt.Analysis MathlibExt.Analysis.PDE.HeatKernel

private theorem exp_growth : HasExpGrowth exp := by
  simpa only [one_mul] using HasExpGrowth.exp_linear 1

private theorem deriv_exp_growth : HasExpGrowth (deriv exp) := by
  simpa only [Real.deriv_exp] using exp_growth

-- An unbounded datum, its actual derivative, and its nonunit-viscosity trace.
example (t x : ℝ) : HasDerivAt (heatSolution exp t) (heatSolution exp t x) x := by
  simpa only [Real.deriv_exp] using
    heatSolution_hasDerivAt_deriv_of_exp_growth contDiff_exp exp_growth deriv_exp_growth t x

example : Tendsto (fun t => heatSolution exp t 0) (𝓝[>] 0) (𝓝 1) := by
  simpa only [exp_zero] using heatSolution_tendsto_zero_of_exp_growth continuous_exp exp_growth 0

example : Tendsto (fun t => deriv (heatSolution exp (3 * t)) 0) (𝓝[>] 0) (𝓝 1) := by
  simpa only [Real.deriv_exp, exp_zero] using
    heatSolution_deriv_tendsto_zero_scaled_of_exp_growth contDiff_exp exp_growth deriv_exp_growth
      (by norm_num : (0 : ℝ) < 3) 0

example : deriv (heatSolution exp 0) 0 = 1 := by
  change deriv (fun x => heatSolution exp 0 x) 0 = 1
  simp

example (t x : ℝ) (ht : 0 < t) : HasDerivAt (fun s => heatSolution exp (3 * s) x)
    (3 * deriv (deriv (heatSolution exp (3 * t))) x) t :=
  heatSolution_hasDerivAt_time_scaled_of_exp_growth continuous_exp.aestronglyMeasurable
    exp_growth (by norm_num) ht x

example (t x : ℝ) : 0 < heatSolution exp t x :=
  heatSolution_pos_of_exp_growth continuous_exp exp_growth exp_pos t x

example : Integrable (fun y : ℝ => heatKernel ℝ (1 / 100) (17 - y) * exp y) :=
  integrable_heatKernel_mul_of_exp_growth continuous_exp.aestronglyMeasurable
    exp_growth (by norm_num) 17

-- Nonsmooth exponentially growing initial data still become jointly smooth.
private theorem exp_abs_growth : HasExpGrowth (fun x : ℝ => exp |x|) := by
  refine ⟨1, 1, by norm_num, by norm_num, fun x => ?_⟩
  simp only [one_mul, abs_of_pos (exp_pos _), le_refl]

example : ContDiffOn ℝ 10 (Function.uncurry (heatSolution (fun x => exp |x|)))
    (Ioi 0 ×ˢ univ) :=
  (heatSolution_contDiffOn_of_exp_growth (by fun_prop) exp_abs_growth).of_le (by simp)

example : Tendsto (fun t => heatSolution (fun x => exp |x|) t 0) (𝓝[>] 0) (𝓝 1) := by
  simpa using heatSolution_tendsto_zero_of_exp_growth (by fun_prop) exp_abs_growth 0

-- All-positive-time integrability also works for signed unbounded data.
example (t x : ℝ) (ht : 0 < t) :
    Integrable (fun y => heatKernel ℝ t (x - y) * (-3 * exp (2 * y))) :=
  integrable_heatKernel_mul_of_exp_growth (by fun_prop)
    ((HasExpGrowth.exp_linear 2).const_mul (-3)) ht x

#print axioms MathlibExt.Analysis.PDE.HeatKernel.heatSolution_hasDerivAt_time_of_exp_growth
#print axioms MathlibExt.Analysis.PDE.HeatKernel.heatSolution_deriv_tendsto_zero_of_exp_growth
