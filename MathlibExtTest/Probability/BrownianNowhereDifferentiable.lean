/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.BrownianMotionExistence
import MathlibExt.Probability.BrownianNowhereDifferentiable

open MeasureTheory ProbabilityTheory Set
open scoped NNReal Topology

namespace MathlibExtTest.Probability.BrownianNowhereDifferentiable

open MathlibExt.Probability.BrownianSamplePathsWanted

-- Exercise the theorem on an existing Brownian motion and check the constant extension.
example : ∃ (P : Measure (ℝ≥0 → ℝ)) (B : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ),
    IsProbabilityMeasure P ∧ IsBrownianReal B P ∧
      ∀ᵐ ω ∂P, (∀ t : ℝ, 0 < t → ¬ DifferentiableAt ℝ (fun s : ℝ ↦ B s.toNNReal ω) t) ∧
        (∀ t : ℝ, t < 0 → HasDerivAt (fun s : ℝ ↦ B s.toNNReal ω) 0 t) := by
  obtain ⟨P, B, hB⟩ := exists_isBrownianReal
  refine ⟨P, B, (hB.hasLaw_eval 0).isProbabilityMeasure, hB, ?_⟩
  filter_upwards [IsBrownianReal.ae_not_differentiableAt (hB := hB)] with ω hω
  refine ⟨hω, fun t ht ↦ ?_⟩
  apply (hasDerivAt_const t (B 0 ω)).congr_of_eventuallyEq
  filter_upwards [Iio_mem_nhds ht] with s hs
  rw [Real.toNNReal_of_nonpos hs.le]

end MathlibExtTest.Probability.BrownianNowhereDifferentiable
