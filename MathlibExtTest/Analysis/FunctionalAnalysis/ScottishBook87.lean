/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.FunctionalAnalysis.ScottishBook87

open MeasureTheory
open scoped ENNReal
open MathlibExt.Analysis.FunctionalAnalysis.ScottishBook87Wanted

private noncomputable abbrev μ := volume.restrict (Set.Icc (0 : ℝ) 1)

-- Pointwise absolute value is nonlinear and satisfies both endpoint estimates with constant one.
private theorem interpolate_abs (α : ℝ≥0∞) (hα : 2 < α) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ f : ℝ → ℝ, MemLp f 2 μ →
      MemLp (fun x ↦ ‖f x‖) 2 μ ∧
        (eLpNorm (fun x ↦ ‖f x‖) 2 μ).toReal ≤ K * (eLpNorm f 2 μ).toReal := by
  apply nonlinearInterpolationLp 1 α le_rfl (lt_trans (by norm_num : (1 : ℝ≥0∞) < 2) hα)
    (fun f x ↦ ‖f x‖) _ _ _ 2 (by norm_num) hα
  · refine ⟨1, zero_le_one, fun f g hf hg ↦ ?_⟩
    rw [one_mul]
    apply ENNReal.toReal_mono (hf.sub hg).eLpNorm_lt_top.ne
    exact eLpNorm_mono (hf.norm.sub hg.norm).aestronglyMeasurable (fun x ↦
      abs_norm_sub_norm_le (f x) (g x))
  · exact fun _ hf ↦ hf.norm
  · refine ⟨1, zero_le_one, fun f hf ↦ ⟨hf.norm, ?_⟩⟩
    rw [eLpNorm_norm f hf.aestronglyMeasurable, one_mul]

-- Exercise both a finite upper endpoint and the essential-supremum endpoint.
example := interpolate_abs 3 (by norm_num)
example := interpolate_abs ⊤ (by simp)
