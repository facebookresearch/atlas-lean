/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.MeasureTheory.Integral.DirichletIntegral
import Mathlib.Order.Filter.AtTopBot.Archimedean

open Filter MeasureTheory Set MathlibExt.MeasureTheory.Integral.ImproperIntegralAbsoluteConditionalWanted
open scoped Topology Interval

-- Natural cutoffs converge too, but this is not a Lebesgue integral on the half-line.
example : (∃ L : ℝ, Tendsto (fun n : ℕ ↦ ∫ x in (1 : ℝ)..(n : ℝ), Real.sin x / x)
    atTop (𝓝 L)) ∧ ¬ Integrable (fun x ↦ Real.sin x / x) (volume.restrict (Ioi 1)) := by
  obtain ⟨_, ⟨L, h⟩, hnon⟩ := dirichlet_integral_conditionally_convergent
  exact ⟨⟨L, h.comp tendsto_natCast_atTop_atTop⟩, hnon⟩
