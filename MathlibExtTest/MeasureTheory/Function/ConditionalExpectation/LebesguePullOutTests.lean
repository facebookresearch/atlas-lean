/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.MeasureTheory.Function.ConditionalExpectation.LebesguePullOut

/-!
# Tests for the pull-out property of the conditional Lebesgue expectation

* A factor that is `∞` on a set where the input vanishes: with `g = ∞` on an `m`-measurable set
  `s` and `X = 0` on `s`, the product `g * X` vanishes, and `condLExp_mul_of_measurable_left` forces
  `μ⁻[X | m] = 0` almost everywhere on `s`. The factor takes the value `∞`, and nothing is
  assumed about `m`, `μ` or σ-finiteness, so a finiteness or σ-finiteness hypothesis on the
  lemma would break this test.
* `condLExp_indicator` in the same generality, with the same conclusion.
-/

namespace MathlibExtTest.LebesguePullOut

open MeasureTheory
open scoped ENNReal

/-- Pull out the factor `s.indicator ∞`, which is `∞` on `s`, where the input vanishes: the
conditional Lebesgue expectation of an input that vanishes on an `m`-measurable set `s` vanishes
almost everywhere on `s`. -/
example {Ω : Type*} {m m0 : MeasurableSpace Ω} (μ : Measure[m0] Ω) {s : Set Ω}
    (hs : MeasurableSet[m] s) {X : Ω → ℝ≥0∞} (hX : AEMeasurable X μ) (hX0 : ∀ ω ∈ s, X ω = 0) :
    ∀ᵐ ω ∂μ, ω ∈ s → μ⁻[X | m] ω = 0 := by
  have hg : Measurable[m] (s.indicator fun _ => (∞ : ℝ≥0∞)) := by measurability
  have hgX : (s.indicator fun _ => (∞ : ℝ≥0∞)) * X = 0 := by
    funext ω
    by_cases hω : ω ∈ s
    · simp [hω, hX0 ω hω]
    · simp [hω]
  have h := condLExp_mul_of_measurable_left hg hX
  rw [hgX, condLExp_zero] at h
  filter_upwards [h] with ω hω hωs
  rw [Pi.zero_apply, Pi.mul_apply, Set.indicator_of_mem hωs] at hω
  exact (mul_eq_zero.mp hω.symm).resolve_left ENNReal.top_ne_zero

/-- The indicator form gives the same conclusion, again with no hypothesis on `m` or `μ`. -/
example {Ω : Type*} {m m0 : MeasurableSpace Ω} (μ : Measure[m0] Ω) {s : Set Ω}
    (hs : MeasurableSet[m] s) {X : Ω → ℝ≥0∞} (hX : AEMeasurable X μ) (hX0 : ∀ ω ∈ s, X ω = 0) :
    ∀ᵐ ω ∂μ, ω ∈ s → μ⁻[X | m] ω = 0 := by
  have hsX : s.indicator X = 0 := by
    funext ω
    by_cases hω : ω ∈ s
    · simp [hω, hX0 ω hω]
    · simp [hω]
  have h := condLExp_indicator hs hX
  rw [hsX, condLExp_zero] at h
  filter_upwards [h] with ω hω hωs
  rw [Pi.zero_apply, Set.indicator_of_mem hωs] at hω
  exact hω.symm

end MathlibExtTest.LebesguePullOut
