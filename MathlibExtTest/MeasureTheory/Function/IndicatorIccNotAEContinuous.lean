/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.MeasureTheory.Function.IndicatorIccNotAEContinuous

open MeasureTheory Set Filter
open MathlibExt.MeasureTheory.IndicatorIccNotAEContinuousWanted

-- Changing the endpoint values does not make a continuous representative possible.
example : ¬ ∃ f : ℝ → ℝ, Continuous f ∧
    (∀ᵐ x ∂volume, f x = (Ioo (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) x) := by
  classical
  rintro ⟨f, hf, hae⟩
  apply not_exists_continuous_ae_eq_indicator_Icc
  refine ⟨f, hf, ?_⟩
  filter_upwards [hae, Ioo_ae_eq_Icc (μ := (volume : Measure ℝ)) (a := 0) (b := 1)] with x hfx hx
  rw [hfx]
  simp only [indicator_apply, hx]
