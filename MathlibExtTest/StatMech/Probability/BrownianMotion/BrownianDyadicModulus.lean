/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.BrownianMotion.BrownianDyadicModulus
public import Mathlib

/-!
# Tests for `MathlibExt.Probability.BrownianMotion.BrownianDyadicModulus`

* `brownianContinuousModification_ae_dyadicModulus`, specialized to the window `N = 1`.
-/

@[expose] public section

open StatMech.SLE MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace MathlibExtTest.StatMech.Probability.BrownianMotion.BrownianDyadicModulus

example : ∀ᵐ ω ∂brownianProductLaw, ∃ n0 : ℕ, ∀ n, n0 ≤ n → ∀ s ∈ Set.Icc (-(1 : ℝ)) 1,
    ∀ t ∈ Set.Icc (-(1 : ℝ)) 1, dist s t < ((brownianDyadicDenominator n : ℕ) : ℝ)⁻¹ →
      edist (brownianContinuousModification s ω) (brownianContinuousModification t ω) ≤
        (513 : ℝ≥0∞) * brownianDyadicThreshold n := by
  filter_upwards [brownianContinuousModification_ae_dyadicModulus] with ω h
  simpa using h 1

end MathlibExtTest.StatMech.Probability.BrownianMotion.BrownianDyadicModulus
