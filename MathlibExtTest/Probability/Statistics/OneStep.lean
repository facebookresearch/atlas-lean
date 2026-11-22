/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.OneStep

/-!
# Tests for the one-step Newton estimator

* Positive: the update at the truth adds the scaled average score `J⁻¹ (n⁻¹ • Sn)` (plus sign).
* Boundary: with zero total score the update stays at the starter.
* Regularity: the projection `fun t _ => t`, in place of the score, satisfies the shapes of the
  differentiability (`hdiff`) and joint-measurability (`hscore_meas`) hypotheses of
  `tendstoInDistribution_oneStep`.
-/

@[expose] public section

namespace MathlibExt.Probability.Statistics.OneStep

-- Positive: at the truth, the Newton correction is the scaled average score (plus sign).
example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (J : E →L[ℝ] E) (Sn : E) (n : ℕ) (θ₀ : E) :
    oneStepUpdate J θ₀ Sn n = θ₀ + Ring.inverse J ((n : ℝ)⁻¹ • Sn) := by
  rfl

-- Boundary: with zero total score the update stays at the starter.
example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (J : E →L[ℝ] E) (θinit : E) (n : ℕ) :
    oneStepUpdate J θinit 0 n = θinit := by
  simp [oneStepUpdate]

-- New-regularity discharge (non-vacuous): the projection score satisfies both new
-- hypotheses by standard lemmas (differentiability of the identity on any ball;
-- measurability of the first projection).
example {𝓧 : Type*} [MeasurableSpace 𝓧] (θ₀ : ℝ) (δ : ℝ) :
    (∀ _ : 𝓧, DifferentiableOn ℝ (fun t : ℝ => t) (Metric.ball θ₀ δ)) ∧
      Measurable (fun q : ℝ × 𝓧 => (fun t _ => t) q.1 q.2) := by
  refine ⟨fun _ => differentiable_id.differentiableOn, ?_⟩
  show Measurable (fun q : ℝ × 𝓧 => q.1)
  exact measurable_fst

end MathlibExt.Probability.Statistics.OneStep
