/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.MeasureTheory.Function.WeakLimitOfNonnegLpNonneg
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

open Filter MeasureTheory Set
open MathlibExt.Analysis.FunctionalAnalysis.WeakLimitOfNonnegLpNonnegWanted
open scoped ENNReal Topology

private noncomputable def μ : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)

private noncomputable def r (n : ℕ) : ℝ := 1 + ((n : ℝ) + 1)⁻¹

-- A nonconstant sequence of positive scalings has a nonzero weak limit.
example : ∃ f : Lp ℝ 2 μ, f =ᵐ[μ] (fun _ => (2 : ℝ)) ∧ ∀ᵐ x ∂μ, 0 ≤ f x := by
  let : IsFiniteMeasure μ := ⟨by
    rw [μ, Measure.restrict_apply_univ, Real.volume_Icc]
    exact ENNReal.ofReal_lt_top⟩
  let h : MemLp (fun _ : ℝ => (2 : ℝ)) 2 μ := memLp_const 2
  let f := h.toLp _
  have hf : f =ᵐ[μ] (fun _ => (2 : ℝ)) := h.coeFn_toLp
  refine ⟨f, hf, ?_⟩
  have hp : (1 : ℝ≥0∞) < 2 ∧ (2 : ℝ≥0∞) < ∞ := ⟨by norm_num, by simp⟩
  apply ae_nonneg_of_weak_tendsto_of_ae_nonneg 2 hp (fun n => r n • f) f
  · intro n
    change ∀ᵐ x ∂μ, 0 ≤ (r n • f) x
    filter_upwards [Lp.coeFn_smul (r n) f, hf] with x hs hx
    change (r n • f) x = r n * f x at hs
    rw [hs, hx]
    unfold r
    positivity
  · intro l
    have hinv : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
    have hr : Tendsto r atTop (𝓝 1) := by
      change Tendsto (fun n : ℕ => 1 + ((n : ℝ) + 1)⁻¹) atTop (𝓝 1)
      simpa only [add_zero] using hinv.const_add 1
    have hlim : Tendsto (fun n : ℕ => r n * l f) atTop (𝓝 (l f)) := by
      simpa only [one_mul] using hr.mul_const (l f)
    refine hlim.congr fun n => ?_
    exact ((l : Lp ℝ 2 μ →L[ℝ] ℝ).map_smul (r n) f).symm
