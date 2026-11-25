/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.PDE.HeatKernelContinuity
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

open MathlibExt.Analysis MathlibExt.Analysis.PDE.HeatKernel

example {f : ℝ → ℝ} (hf : Continuous f) (hg : HasExpGrowth f) :
    Continuous (Function.uncurry (heatSolution f)) :=
  heatSolution_continuous_of_exp_growth hf hg

open Real Filter Topology Set MeasureTheory
open scoped ContDiff

private theorem exp_growth : HasExpGrowth exp := by
  simpa only [one_mul] using HasExpGrowth.exp_linear 1

-- No boundedness of the datum and no uniform positive lower bound are needed.
example : Continuous (Function.uncurry (heatSolution exp)) :=
  heatSolution_continuous_of_exp_growth continuous_exp exp_growth

example : Continuous (fun p : ℝ × ℝ => deriv (heatSolution exp p.1) p.2) :=
  heatSolution_deriv_continuous_of_exp_growth contDiff_exp exp_growth
    (by simpa only [Real.deriv_exp] using exp_growth)

-- The actual initial derivative is recovered while the position moves.
example : Tendsto (fun t : ℝ => deriv (heatSolution exp t) (sqrt t)) (𝓝[>] 0) (𝓝 1) := by
  have hc := (heatSolution_deriv_continuous_of_exp_growth contDiff_exp exp_growth
    (by simpa only [Real.deriv_exp] using exp_growth)).comp
    (continuous_id.prodMk continuous_sqrt)
  have hz : deriv (heatSolution exp 0) 0 = 1 := by
    change deriv (fun x => heatSolution exp 0 x) 0 = 1
    simp
  simpa only [Function.comp_def, id_eq, sqrt_zero, hz] using!
    hc.continuousAt.continuousWithinAt.tendsto (s := Ioi (0 : ℝ)) (x := 0)

private theorem exp_abs_growth : HasExpGrowth (fun x : ℝ => exp |x|) := by
  refine ⟨1, 1, by norm_num, by norm_num, fun x => ?_⟩
  simp only [one_mul, abs_of_pos (exp_pos _), le_refl]

-- A corner in the initial datum does not obstruct joint continuity.
example : Continuous (Function.uncurry (heatSolution (fun x => exp |x|))) :=
  heatSolution_continuous_of_exp_growth (by fun_prop) exp_abs_growth

example : Tendsto (fun p : ℝ × ℝ => heatSolution (fun x => exp |x|) p.1 p.2)
    (𝓝 (0, 0)) (𝓝 1) := by
  simpa only [Function.uncurry_def, heatSolution_zero, abs_zero, exp_zero] using!
    (heatSolution_continuous_of_exp_growth (by fun_prop) exp_abs_growth).tendsto (0, 0)

-- Unbounded data are ordered using genuine integrable convolutions.
example (t x : ℝ) : heatSolution exp t x ≤ heatSolution (fun y => 2 * exp y) t x :=
  heatSolution_mono_of_exp_growth continuous_exp.aestronglyMeasurable (by fun_prop)
    exp_growth (exp_growth.const_mul 2) (fun y => by linarith [exp_pos y]) t x

-- Nonpositive times use the stationary extension, not a backward heat flow.
example (x : ℝ) : heatSolution (fun y => exp |y|) (-3) x = exp |x| :=
  heatSolution_of_nonpos _ (by norm_num) x

example (f : ℝ → ℝ) (x : ℝ) :
    f x = ∫ y, heatKernel ℝ 1 y * f (x - sqrt (-2) * y) := by
  simpa only [heatSolution_of_nonpos f (by norm_num : (-2 : ℝ) ≤ 0)] using
    heatSolution_rescaled_all f (-2) x

#print axioms MathlibExt.Analysis.PDE.HeatKernel.heatSolution_continuous_of_exp_growth
#print axioms MathlibExt.Analysis.PDE.HeatKernel.heatSolution_mono_of_exp_growth
