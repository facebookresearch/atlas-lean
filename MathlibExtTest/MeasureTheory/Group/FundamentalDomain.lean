/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.MeasureTheory.Group.FundamentalDomain

@[expose] public section

open MeasureTheory
open scoped Pointwise

example {G X ι : Type*} [Group G] [MulAction G X] [MeasurableSpace X] [Countable ι]
    (μ : Measure X) (Γ₁ Γ₂ : Subgroup G) (hle : Γ₂ ≤ Γ₁) [Countable Γ₁]
    [MeasurableSpace G] [MeasurableSMul G X] [SMulInvariantMeasure G X μ]
    (𝓕 : Set X) (h𝓕 : IsFundamentalDomain Γ₁ 𝓕 μ)
    (R : ι → Γ₁) (hR : ∀ γ : Γ₁, ∃! i, ((R i)⁻¹ * γ : G) ∈ Γ₂) :
    IsFundamentalDomain Γ₂ (⋃ i, ((R i : G)⁻¹) • 𝓕) μ :=
  MeasureTheory.IsFundamentalDomain.iUnion_inv_smul_of_leftCosetRepresentatives μ Γ₁ Γ₂ hle 𝓕 h𝓕 R hR
