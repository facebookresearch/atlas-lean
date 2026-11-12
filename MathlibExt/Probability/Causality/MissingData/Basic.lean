/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Causality.CausalIdentification

/-!
# Missing-at-random and response-positivity predicates

Shared hypotheses for identification and augmented inverse probability weighting with a
missing outcome, in the common `MissingOutcomes` namespace.
-/

@[expose] public section

open MeasureTheory Finset

namespace MathlibExt.Probability.Causality.MissingOutcomes

variable {Ω 𝒳 : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Missing at random** (Rubin 1976), for a discrete covariate: the response event `R` is
conditionally independent of the outcome `Y` given `X`, stated through joint probabilities,
`P(R, Y ∈ B, X = x) P(X = x) = P(R, X = x) P(Y ∈ B, X = x)`. It holds vacuously when every
level set `{X = x}` is null (an atomless `X`); interpret it as conditional independence only
for a covariate with countably many values. -/
def MissingAtRandom (μ : Measure Ω) (R : Set Ω) (Y : Ω → ℝ) (X : Ω → 𝒳) : Prop :=
  CondIndepDiscrete μ R Y X

/-- **Positivity** of the response: `P(R | X = x) ≥ ε` for some `ε > 0` and every covariate
value of positive probability. -/
def ResponsePositivity (μ : Measure Ω) (R : Set Ω) (X : Ω → 𝒳) : Prop :=
  ∃ ε > 0, ∀ x, μ (X ⁻¹' {x}) ≠ 0 → ε ≤ propensity μ R X x

/-- For a covariate with finitely many values, positivity is the pointwise condition
`P(R | X = x) > 0` on values of positive probability. -/
theorem responsePositivity_iff [Finite 𝒳] {R : Set Ω} {X : Ω → 𝒳} :
    ResponsePositivity μ R X ↔ ∀ x, μ (X ⁻¹' {x}) ≠ 0 → 0 < propensity μ R X x := by
  constructor
  · rintro ⟨ε, hε, h⟩ x hx
    exact hε.trans_le (h x hx)
  · intro h
    have := Fintype.ofFinite 𝒳
    classical
    set S := univ.filter fun x => μ (X ⁻¹' {x}) ≠ 0
    rcases S.eq_empty_or_nonempty with hS | hS
    · refine ⟨1, one_pos, fun x hx => ?_⟩
      have hx' : x ∈ S := mem_filter.2 ⟨mem_univ x, hx⟩
      simp [hS] at hx'
    · obtain ⟨x₀, hx₀, hmin⟩ := S.exists_min_image (fun x => propensity μ R X x) hS
      exact ⟨_, h x₀ (mem_filter.1 hx₀).2, fun x hx => hmin x (mem_filter.2 ⟨mem_univ x, hx⟩)⟩

end MathlibExt.Probability.Causality.MissingOutcomes
