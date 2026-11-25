/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import MathlibExt.Analysis.Complex.LaurentSeries

open MathlibExt.Analysis.Complex.LaurentSeriesWanted

-- A pole at the center is allowed. The same coefficients work on two distinct circles.
example : ∃ a : ℤ → ℂ, HasSum (fun n : ℤ ↦ a n * (-1 : ℂ) ^ n) (-1) ∧
    HasSum (fun n : ℤ ↦ a n * (2 : ℂ) ^ n) (2 : ℂ)⁻¹ := by
  have hf : DifferentiableOn ℂ (fun z : ℂ ↦ (z - 1)⁻¹)
      {z : ℂ | 0 < ‖z - 1‖ ∧ ‖z - 1‖ < 3} :=
    (differentiableOn_id.sub_const 1).fun_inv fun _ hz ↦ norm_pos_iff.mp hz.1
  obtain ⟨a, ha⟩ := laurentExpansion hf
  refine ⟨a, ?_, ?_⟩
  · simpa using ha 0 (by norm_num)
  · have h : (3 : ℂ) - 1 = 2 := by norm_num
    simpa [h] using ha 3 (by norm_num [h])

-- When the center belongs to the domain, evaluation there recovers the constant coefficient.
example : ∃ a : ℤ → ℂ, a 0 = 3 ∧ ∀ z : ℂ, ‖z‖ < 1 →
    HasSum (fun n : ℤ ↦ a n * z ^ n) (z + 3) := by
  obtain ⟨a, ha⟩ := laurentExpansion (c := 0) (r := -1) (R := 1)
    (f := fun z ↦ z + 3) (differentiableOn_id.add_const 3)
  have hcenter : HasSum (fun n : ℤ ↦ a n * (0 : ℂ) ^ n) (a 0) := by
    simpa using hasSum_single (f := fun n : ℤ ↦ a n * (0 : ℂ) ^ n) 0
      (fun n hn ↦ by simp [zero_zpow _ hn])
  refine ⟨a, hcenter.unique (by simpa using ha 0 (by norm_num)), fun z hz ↦ ?_⟩
  simpa using ha z ⟨by simpa using (neg_one_lt_zero.trans_le (norm_nonneg z)), by simpa using hz⟩
