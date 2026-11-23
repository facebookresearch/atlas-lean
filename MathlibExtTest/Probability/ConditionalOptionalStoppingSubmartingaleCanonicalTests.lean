/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.ConditionalOptionalStoppingSubmartingale
public import MathlibExt.Probability.OptionalStoppingUniformIntegrable

@[expose] public section
open MeasureTheory Filter

namespace MathlibExtTest.Probability.ConditionalOptionalStoppingSubmartingaleCanonicalTests

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ℱ : Filtration ℕ ‹MeasurableSpace Ω›}

/-- Whole-process UI submartingales use the existing canonical stopped value at infinity. -/
theorem canonical_whole_UI_conditional {f : ℕ → Ω → ℝ}
    (hsub : Submartingale f ℱ μ) (hui : UniformIntegrable f 1 μ)
    {L M : Ω → WithTop ℕ} (hL : IsStoppingTime ℱ L) (hM : IsStoppingTime ℱ M)
    (hLM : L ≤ M) :
    stoppedValueAtTop f L ≤ᵐ[μ] μ[stoppedValueAtTop f M | hL.measurableSpace] :=
  hsub.stoppedValueAtTop_le_condExp_stoppedValueAtTop hui hL hM hLM

/-- Integral monotonicity has the same whole-process UI contract and canonical value. -/
theorem canonical_whole_UI_integral {f : ℕ → Ω → ℝ}
    (hsub : Submartingale f ℱ μ) (hui : UniformIntegrable f 1 μ)
    {L M : Ω → WithTop ℕ} (hL : IsStoppingTime ℱ L) (hM : IsStoppingTime ℱ M)
    (hLM : L ≤ M) :
    ∫ ω, stoppedValueAtTop f L ω ∂μ ≤ ∫ ω, stoppedValueAtTop f M ω ∂μ :=
  hsub.integral_stoppedValueAtTop_mono_of_uniformIntegrable hui hL hM hLM

end MathlibExtTest.Probability.ConditionalOptionalStoppingSubmartingaleCanonicalTests
