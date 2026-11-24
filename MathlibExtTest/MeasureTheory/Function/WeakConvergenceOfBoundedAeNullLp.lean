/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.MeasureTheory.Function.WeakConvergenceOfBoundedAeNullLp
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

open Filter MeasureTheory Set
open MathlibExt.Analysis.FunctionalAnalysis.WeakConvergenceOfBoundedAeNullLpWanted
open scoped ENNReal Topology

private noncomputable def scale (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

-- Nonzero constants converging to zero pair to zero against every L² test function.
example : ∃ f : ℕ → Lp ℝ 2 μI01,
    (∀ n, f n =ᵐ[μI01] (fun _ : ℝ => scale n)) ∧
    ∀ g : Lp ℝ 2 μI01, Tendsto (fun n => ∫ x, f n x * g x ∂μI01) atTop (𝓝 0) := by
  have hmass : μI01 univ = 1 := by rw [μI01, Measure.restrict_apply_univ, Real.volume_Ioo]; norm_num
  let : IsProbabilityMeasure μI01 := ⟨hmass⟩
  have hμ : μI01 ≠ 0 := by
    intro he
    simp [he] at hmass
  let hf (n : ℕ) : MemLp (fun _ : ℝ => scale n) 2 μI01 := memLp_const (scale n)
  let f (n : ℕ) := (hf n).toLp _
  have hcoe (n : ℕ) : f n =ᵐ[μI01] (fun _ : ℝ => scale n) := (hf n).coeFn_toLp
  refine ⟨f, hcoe, ?_⟩
  have h22 : (1 : ℝ≥0∞) / 2 + 1 / 2 = 1 := by
    simpa using ENNReal.HolderTriple.one_div_add_one_div (2 : ℝ≥0∞) 2 1
  apply tendsto_integral_mul_of_ae_tendsto_zero_of_eLpNorm_le_one 2 2 (by simp) (by norm_num) h22
  · intro n
    rw [eLpNorm_congr_ae (hcoe n), eLpNorm_const _ (by norm_num : (2 : ℝ≥0∞) ≠ 0) hμ,
      hmass, ENNReal.one_rpow, mul_one, ← ofReal_norm, Real.norm_eq_abs,
      abs_of_nonneg (by unfold scale; positivity)]
    simpa using ENNReal.ofReal_le_ofReal (show scale n ≤ 1 from
      (div_le_one (by positivity)).mpr (le_add_of_nonneg_left (Nat.cast_nonneg n)))
  · have hlim : Tendsto scale atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    filter_upwards [ae_all_iff.mpr hcoe] with x hx
    exact hlim.congr fun n => (hx n).symm
