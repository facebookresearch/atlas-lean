/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.MultipleTesting.Basic
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-!
# Fixed-sample confidence sets by test inversion

Given tests indexed by estimand values `t`, with measurable rejection sets `R t`, the inverted
confidence set at `x` is `confSetOfTests R x = {t | x ∉ R t}`. For a model `P : Θ → Measure X`
and an estimand `τ : Θ → T`, level `α` at every parameter (each null is an estimand fiber) is
equivalent to coverage `1 - α` of the inverted set at every parameter. A valid p-value
(`IsValidPValue`) thresholded at `α` is a level-`α` test by definition, so inverting valid
p-values gives coverage `1 - α`.

## Main definitions

* `confSetOfTests`

## Main results

* `coverage_iff_level`: level at every parameter iff coverage at every parameter.
* `coverage_of_isValidPValue`: inverting valid p-values gives coverage `1 - α`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace MathlibExt.Probability.Statistics

open MathlibExt.Probability.Statistics.MultipleTesting

/-- The confidence set obtained by inverting the family of tests `R`: the estimand values `t`
whose test `R t` does not reject the observation `x`. -/
def confSetOfTests {X T : Type*} (R : T → Set X) (x : X) : Set T :=
  {t | x ∉ R t}

/-- **Test inversion.** For estimand-indexed tests with measurable rejection sets, level `α` at
every parameter (each null is the estimand fiber) is equivalent to coverage `1 - α` of the
inverted confidence set at every parameter. -/
theorem coverage_iff_level {Θ X T : Type*} [MeasurableSpace X]
    (P : Θ → Measure X) [∀ θ, IsProbabilityMeasure (P θ)] (τ : Θ → T) (R : T → Set X)
    (hR : ∀ t, MeasurableSet (R t)) {α : ℝ} :
    (∀ θ, (P θ).real (R (τ θ)) ≤ α) ↔
      ∀ θ, 1 - α ≤ (P θ).real {x | τ θ ∈ confSetOfTests R x} := by
  refine forall_congr' fun θ => ?_
  rw [show {x | τ θ ∈ confSetOfTests R x} = (R (τ θ))ᶜ from rfl, probReal_compl_eq_one_sub (hR _)]
  constructor <;> intro h <;> linarith

/-- **Inverting valid p-values.** If `p t` is a measurable p-value for the null `τ θ = t`, valid
at the true estimand under every `P θ`, the inverted confidence set has coverage `1 - α`. -/
theorem coverage_of_isValidPValue {Θ X T : Type*} [MeasurableSpace X]
    (P : Θ → Measure X) [∀ θ, IsProbabilityMeasure (P θ)] (τ : Θ → T) (p : T → X → ℝ)
    (hp : ∀ t, Measurable (p t)) (hvalid : ∀ θ, IsValidPValue (P θ) (p (τ θ)))
    {α : ℝ} (hα : α ∈ Set.Icc (0 : ℝ) 1) (θ : Θ) :
    1 - α ≤ (P θ).real {x | τ θ ∈ confSetOfTests (fun t => {y | p t y ≤ α}) x} := by
  refine (coverage_iff_level P τ (fun t => {y | p t y ≤ α})
    (fun t => measurableSet_le (hp t) measurable_const)).1 (fun θ' => ?_) θ
  rw [measureReal_def]
  exact ENNReal.toReal_le_of_le_ofReal hα.1 ((hvalid θ') α hα)

end MathlibExt.Probability.Statistics
