/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.MeasureTheory.Group.FundamentalDomainIntegral

open MeasureTheory
open scoped Pointwise ENNReal

/-- Smoke test: the theorem applies with abstract data. -/
example {G X ι : Type*} [Group G] [MulAction G X] [MeasurableSpace X] [Countable ι]
    (μ : Measure X) (Γ₁ Γ₂ : Subgroup G) (_hle : Γ₂ ≤ Γ₁) [Countable Γ₁]
    [MeasurableSpace G] [MeasurableSMul G X] [SMulInvariantMeasure G X μ]
    (𝓕 : Set X) (h𝓕 : IsFundamentalDomain Γ₁ 𝓕 μ)
    (R : ι → Γ₁) (hR : ∀ γ : Γ₁, ∃! i, ((R i)⁻¹ * γ : G) ∈ Γ₂) :
    (∀ f : X → ℝ≥0∞, Measurable f →
      ∫⁻ x in ⋃ i, ((R i : G)⁻¹) • 𝓕, f x ∂μ = ∫⁻ x in 𝓕, ∑' i, f ((R i : G)⁻¹ • x) ∂μ) ∧
    ∀ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (h : X → E),
      AEStronglyMeasurable h μ →
      ∫⁻ x in 𝓕, ∑' i, ‖h ((R i : G)⁻¹ • x)‖ₑ ∂μ < ∞ →
      IntegrableOn h (⋃ i, ((R i : G)⁻¹) • 𝓕) μ ∧
      (∀ᵐ x ∂μ.restrict 𝓕, Summable fun i => ‖h ((R i : G)⁻¹ • x)‖) ∧
      ∫ x in ⋃ i, ((R i : G)⁻¹) • 𝓕, h x ∂μ = ∫ x in 𝓕, ∑' i, h ((R i : G)⁻¹ • x) ∂μ :=
  IsFundamentalDomain.setLIntegral_iUnion_inv_smul_eq_and_setIntegral_eq_of_leftCosetRepresentatives
    μ Γ₁ Γ₂ _hle 𝓕 h𝓕 R hR
