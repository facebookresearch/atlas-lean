/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.PDE.HeatKernelSmoothness
import Mathlib.Tactic.NormNum

open Set MeasureTheory Filter Topology
open scoped ContDiff
open MathlibExt.Analysis.PDE.HeatKernel

example (f : ℝ → ℝ) (hf : Continuous f) (hb : ∃ M, ∀ x, |f x| ≤ M) :
    ContDiffOn ℝ ∞ (Function.uncurry (heatSolution f)) (Ioi 0 ×ˢ univ) :=
  heatSolution_contDiffOn hf.aestronglyMeasurable hb

example (f : ℝ → ℝ) (hf : Continuous f) (hb : ∃ M, ∀ x, |f x| ≤ M)
    (ν : ℝ) (hν : 0 < ν) :
    ContDiffOn ℝ 3 (fun p : ℝ × ℝ => heatSolution f (ν * p.1) p.2) (Ioi 0 ×ˢ univ) :=
  (heatSolution_contDiffOn_scaled hf.aestronglyMeasurable hb hν).of_le (by simp)

private noncomputable def step (x : ℝ) : ℝ := (Ici (0 : ℝ)).indicator (fun _ => 1) x

private theorem step_measurable : AEStronglyMeasurable step :=
  (measurable_const.indicator measurableSet_Ici).aestronglyMeasurable

private theorem step_bound (x : ℝ) : |step x| ≤ 1 := by
  by_cases hx : 0 ≤ x <;> simp [step, hx]

-- A discontinuous bounded datum smooths jointly on the entire positive-time half-plane.
example : ContDiffOn ℝ ∞ (Function.uncurry (heatSolution step)) (Ioi 0 ×ˢ univ) :=
  heatSolution_contDiffOn step_measurable ⟨1, step_bound⟩

example : ContDiffAt ℝ ∞ (Function.uncurry (heatSolution step)) (1, 0) :=
  heatSolution_contDiffAt step_measurable ⟨1, step_bound⟩ (by norm_num)

-- Actual joint differentiability, including points where the datum jumps.
example : DifferentiableAt ℝ (Function.uncurry (heatSolution step)) (1, 0) :=
  (heatSolution_contDiffAt step_measurable ⟨1, step_bound⟩ (by norm_num)).differentiableAt (by simp)

-- The local C3 interface has no restriction on the spatial domain.
example : ContDiffOn ℝ 3 (Function.uncurry (heatSolution step))
    (Ioo (0 : ℝ) 2 ×ˢ Ioo (-3 : ℝ) 4) :=
  (heatSolution_contDiffOn_rectangle step_measurable ⟨1, step_bound⟩
    Set.Ioo_subset_Ioi_self).of_le (by simp)

example : ContDiffOn ℝ 8 (fun p : ℝ × ℝ => heatSolution step (3 * p.1) p.2)
    (Ioi 0 ×ˢ univ) :=
  (heatSolution_contDiffOn_scaled step_measurable ⟨1, step_bound⟩
    (by norm_num : (0 : ℝ) < 3)).of_le (by simp)

-- The joint derivative itself has all finite regularity orders locally.
example : ContDiffOn ℝ 2 (fderiv ℝ (Function.uncurry (heatSolution step)))
    (Ioi 0 ×ˢ univ) :=
  (heatSolution_contDiffOn step_measurable ⟨1, step_bound⟩).fderiv_of_isOpen
    (isOpen_Ioi.prod isOpen_univ) (by simp)

-- Negative data and nonintegrable constants are accepted without special cases.
example : ContDiffOn ℝ ∞ (Function.uncurry (heatSolution (fun _ => (-2 : ℝ))))
    (Ioi 0 ×ˢ univ) :=
  heatSolution_contDiffOn aestronglyMeasurable_const ⟨2, fun _ => by norm_num⟩

example (t x : ℝ) : heatSolution (fun _ => (-2 : ℝ)) t x = -2 := heatSolution_const _ _ _

private theorem step_not_continuousAt_zero : ¬ ContinuousAt step 0 := by
  have hl : Filter.Tendsto step (nhdsWithin (0 : ℝ) (Iio 0)) (nhds 0) := by
    apply Filter.Tendsto.congr' (f₁ := fun _ : ℝ => (0 : ℝ)) ?_ tendsto_const_nhds
    filter_upwards [self_mem_nhdsWithin] with x hx
    simp [step, not_le.mpr hx]
  intro hc
  have he := tendsto_nhds_unique hl (hc.tendsto.mono_left inf_le_left)
  simp [step] at he

-- Positive time is essential: the chosen time-zero extension retains the jump.
example : ¬ ContinuousAt (Function.uncurry (heatSolution step)) (0, 0) := by
  intro hc
  apply step_not_continuousAt_zero
  have h := hc.comp (x := (0 : ℝ)) (continuousAt_const.prodMk continuousAt_id)
  simpa only [Function.comp_def, Function.uncurry_apply_pair, heatSolution_zero] using! h

#print axioms MathlibExt.Analysis.PDE.HeatKernel.heatSolution_contDiffOn
