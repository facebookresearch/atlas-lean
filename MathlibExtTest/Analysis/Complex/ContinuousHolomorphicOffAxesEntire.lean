/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Complex.ContinuousHolomorphicOffAxesEntire
import Mathlib.Analysis.Complex.CauchyIntegral

open MathlibExt.Analysis.Complex.ContinuousHolomorphicOffAxesEntireWanted

-- The conclusion includes the axes' intersection and nonzero points on an axis.
example (f : ℂ → ℂ) (hc : Continuous f)
    (h : ∀ z : ℂ, z.re ≠ 0 → z.im ≠ 0 → DifferentiableAt ℂ f z) :
    AnalyticAt ℂ f 0 ∧ AnalyticAt ℂ f Complex.I := by
  have he : Differentiable ℂ f :=
    differentiable_of_continuous_of_differentiableOn_compl_coordAxes f hc (by
      intro z hz
      have hz' : ¬ (z.im = 0 ∨ z.re = 0) := hz
      exact (h z (fun hr ↦ hz' (Or.inr hr)) (fun hi ↦ hz' (Or.inl hi))).differentiableWithinAt)
  exact ⟨he.analyticAt 0, he.analyticAt Complex.I⟩
