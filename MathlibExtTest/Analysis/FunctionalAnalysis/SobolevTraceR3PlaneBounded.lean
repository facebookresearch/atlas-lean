/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Analysis.FunctionalAnalysis.SobolevTraceR3PlaneBounded
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# Tests for the Sobolev trace bound

The trace estimate yields a uniform bound in Mathlib's real-valued L² norm.
Among constant functions, precisely zero satisfies the energy integrability hypothesis.
-/

open MeasureTheory
open MathlibExt.Analysis.FunctionalAnalysis.SobolevTraceR3PlaneBoundedWanted

example (f : ℕ → ℝ × ℝ × ℝ → ℝ) (hf : ∀ n, ContDiff ℝ 1 (f n))
    (hE : ∀ n, Integrable (fun x => ‖f n x‖ ^ 2 + ‖fderiv ℝ (f n) x‖ ^ 2) ∧
      (∫ x, ‖f n x‖ ^ 2 + ‖fderiv ℝ (f n) x‖ ^ 2) ≤ 1) :
    ∃ M : ℝ, ∀ n, MemLp (fun p : ℝ × ℝ => f n (p.1, p.2, 0)) 2 volume ∧
      lpNorm (fun p : ℝ × ℝ => f n (p.1, p.2, 0)) 2 volume ≤ M := by
  obtain ⟨C, _, hC⟩ := exists_bound_integral_sq_trace_of_integral_sq_add_fderiv_sq_le_one f hf hE
  refine ⟨√C, fun n => ?_⟩
  have hc : Continuous fun p : ℝ × ℝ => f n (p.1, p.2, 0) := by
    fun_prop (disch := exact (hf n).continuous)
  refine ⟨(memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).2 (hC n).1, ?_⟩
  rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num) hc.aestronglyMeasurable]
  simpa [Real.sqrt_eq_rpow, one_div] using Real.sqrt_le_sqrt (hC n).2

example (c : ℝ) :
    Integrable (fun x : ℝ × ℝ × ℝ => ‖c‖ ^ 2 + ‖fderiv ℝ (fun _ : ℝ × ℝ × ℝ => c) x‖ ^ 2) ↔
      c = 0 := by
  have hvol : volume (Set.univ : Set (ℝ × ℝ × ℝ)) = ⊤ := by
    rw [← Set.univ_prod_univ, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_univ]
    rw [← Set.univ_prod_univ (α := ℝ) (β := ℝ), Measure.volume_eq_prod, Measure.prod_prod,
      Real.volume_univ]
    simp
  simp [integrable_const_iff, isFiniteMeasure_iff, hvol]
