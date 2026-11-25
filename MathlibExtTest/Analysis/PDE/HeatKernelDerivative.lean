/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.PDE.HeatKernelDerivative
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.NormNum

open Filter Topology Real MeasureTheory
open MathlibExt.Analysis.PDE.HeatKernel

example (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (hb : ∃ M, ∀ x, |f x| ≤ M) (hdb : ∃ M, ∀ x, |deriv f x| ≤ M) (x : ℝ) :
    Tendsto (fun t => deriv (heatSolution f t) x) (𝓝[>] 0) (𝓝 (deriv f x)) :=
  heatSolution_deriv_tendsto_zero hf hb hdb x

private theorem sin_bound : ∃ M, ∀ x : ℝ, |sin x| ≤ M := ⟨1, abs_sin_le_one⟩

private theorem sin_deriv_bound : ∃ M, ∀ x : ℝ, |deriv sin x| ≤ M :=
  ⟨1, fun x => by simpa only [Real.deriv_sin] using abs_cos_le_one x⟩

-- The derivative commutes with a nonconstant heat evolution, at all times.
example (t x : ℝ) : HasDerivAt (heatSolution sin t) (heatSolution cos t x) x := by
  simpa only [Real.deriv_sin] using
    heatSolution_hasDerivAt_deriv contDiff_sin sin_bound sin_deriv_bound t x

example (t x : ℝ) : deriv (heatSolution sin t) x = heatSolution cos t x := by
  simpa only [Real.deriv_sin] using deriv_heatSolution contDiff_sin sin_bound sin_deriv_bound t x

example : Tendsto (fun t => deriv (heatSolution sin t) 0) (𝓝[>] 0) (𝓝 1) := by
  simpa only [Real.deriv_sin, cos_zero] using
    heatSolution_deriv_tendsto_zero contDiff_sin sin_bound sin_deriv_bound 0

-- Viscosity rescales time; it does not multiply the spatial initial derivative.
example : Tendsto (fun t => deriv (heatSolution sin (3 * t)) 0) (𝓝[>] 0) (𝓝 1) := by
  simpa only [Real.deriv_sin, cos_zero] using
    heatSolution_deriv_tendsto_zero_scaled contDiff_sin sin_bound sin_deriv_bound
      (by norm_num : (0 : ℝ) < 3) 0

example (t x : ℝ) : |deriv (heatSolution sin t) x| ≤ 1 :=
  abs_deriv_heatSolution_le contDiff_sin sin_bound
    (fun y => by simpa only [Real.deriv_sin] using abs_cos_le_one y) t x

-- The extension also preserves the actual derivative at and before time zero.
example : deriv (heatSolution sin 0) 0 = 1 := by
  rw [deriv_heatSolution contDiff_sin sin_bound sin_deriv_bound]
  simp

example : deriv (heatSolution sin (-1)) 0 = 1 := by
  rw [deriv_heatSolution contDiff_sin sin_bound sin_deriv_bound,
    heatSolution_of_nonpos _ (by norm_num)]
  simp

-- Initial data need not be integrable; nonzero constants have zero derivative.
example : ¬ Integrable (fun _ : ℝ => (-2 : ℝ)) := by
  simp [integrable_const_iff, isFiniteMeasure_iff]

example (t x : ℝ) : deriv (heatSolution (fun _ => (-2 : ℝ)) t) x = 0 := by
  change deriv (fun y => heatSolution (fun _ => (-2 : ℝ)) t y) x = 0
  simp only [heatSolution_const, deriv_const]

#print axioms MathlibExt.Analysis.PDE.HeatKernel.heatSolution_deriv_tendsto_zero
