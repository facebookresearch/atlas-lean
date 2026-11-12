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
public import Mathlib.Probability.CDF

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

* `level_iff_coverage`: level at every parameter iff coverage at every parameter.
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
theorem level_iff_coverage {Θ X T : Type*} [MeasurableSpace X]
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
  refine (level_iff_coverage P τ (fun t => {y | p t y ≤ α})
    (fun t => measurableSet_le (hp t) measurable_const)).1 (fun θ' => ?_) θ
  rw [measureReal_def]
  exact ENNReal.toReal_le_of_le_ofReal hα.1 ((hvalid θ') α hα)

/-- Coverage transfers outward along pointwise set inclusion. -/
theorem coverage_mono_of_subset {Θ X T : Type*} [MeasurableSpace X]
    (P : Θ → Measure X) [∀ θ, IsProbabilityMeasure (P θ)]
    (τ : Θ → T) {C C' : X → Set T} (hsub : ∀ x, C x ⊆ C' x) {α : ℝ}
    (hcov : ∀ θ, 1 - α ≤ (P θ).real {x | τ θ ∈ C x}) (θ : Θ) :
    1 - α ≤ (P θ).real {x | τ θ ∈ C' x} := by
  refine le_trans (hcov θ) ?_
  refine measureReal_mono ?h ?_
  · intro x hx
    exact hsub x hx
  · exact measure_ne_top _ _

/-- Coverage transfers outward up to a per-parameter exception budget. -/
theorem coverage_of_subset_ae_budget {Θ X T : Type*} [MeasurableSpace X]
    (P : Θ → Measure X) [∀ θ, IsProbabilityMeasure (P θ)]
    (τ : Θ → T) {C C' : X → Set T} {α : ℝ} {ε : Θ → ℝ}
    (hcov : ∀ θ, 1 - α ≤ (P θ).real {x | τ θ ∈ C x})
    (hbad : ∀ θ, (P θ).real {x | τ θ ∈ C x ∧ τ θ ∉ C' x} ≤ ε θ) (θ : Θ) :
    1 - α - ε θ ≤ (P θ).real {x | τ θ ∈ C' x} := by
  have hsub : {x | τ θ ∈ C x} ⊆ {x | τ θ ∈ C' x} ∪ {x | τ θ ∈ C x ∧ τ θ ∉ C' x} := by
    intro x hx
    by_cases h : τ θ ∈ C' x
    · exact Or.inl h
    · exact Or.inr ⟨hx, h⟩
  have hmono : (P θ).real {x | τ θ ∈ C x}
      ≤ (P θ).real ({x | τ θ ∈ C' x} ∪ {x | τ θ ∈ C x ∧ τ θ ∉ C' x}) :=
    measureReal_mono hsub (measure_ne_top _ _)
  have hunion := measureReal_union_le (μ := P θ)
    {x | τ θ ∈ C' x} {x | τ θ ∈ C x ∧ τ θ ∉ C' x}
  have hcovθ := hcov θ
  have hbadθ := hbad θ
  linarith

/-- **Projected point-test coverage (probability coverage).** A set-valued map containing
the non-rejected estimand image inherits the `1 - α` probability lower bound through the
measurable complement and larger-set probability finiteness. -/
theorem coverage_of_projected_pointTests
    {Θ X T : Type*} [MeasurableSpace X]
    (P : Θ → Measure X) [∀ θ, IsProbabilityMeasure (P θ)]
    (τ : Θ → T)
    (R : Θ → Set X) (hR : ∀ θ, MeasurableSet (R θ))
    {α : ℝ} (hα : α ∈ Set.Icc 0 1) (hlev : ∀ θ, (P θ).real (R θ) ≤ α)
    (C : X → Set T) (hC : ∀ x, {t | ∃ θ, τ θ = t ∧ x ∉ R θ} ⊆ C x)
    (hCmeas : ∀ θ, MeasurableSet {x | τ θ ∈ C x}) :
    ∀ θ, 1 - α ≤ (P θ).real {x | τ θ ∈ C x} := by
  intro θ
  -- The coverage event is measurable, so the bound below is a probability statement.
  have _hCθ : MeasurableSet {x | τ θ ∈ C x} := hCmeas θ
  have hsub : {x | x ∉ R θ} ⊆ {x | τ θ ∈ C x} := fun x hx => hC x ⟨θ, rfl, hx⟩
  have hcompl : {x | x ∉ R θ} = (R θ)ᶜ := rfl
  have hprob : (P θ).real ((R θ)ᶜ) = 1 - (P θ).real (R θ) :=
    probReal_compl_eq_one_sub (hR θ)
  have hmono : (P θ).real {x | x ∉ R θ} ≤ (P θ).real {x | τ θ ∈ C x} :=
    measureReal_mono hsub (measure_ne_top _ _)
  rw [hcompl] at hmono
  have hle := hlev θ
  linarith

/-- A cutoff above the `(1 - α)` cdf level gives a level-`α` one-sided test. -/
theorem measureReal_lt_le_of_le_cdf {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {T : Ω → ℝ} (hT : HasLaw T ν P) {α c : ℝ}
    (hc : 1 - α ≤ cdf ν c) : P.real {ω | c < T ω} ≤ α := by
  have h1 : P.real {ω | c < T ω} = ν.real {x | c < x} :=
    hT.measureReal_eq (p := fun x => c < x) measurableSet_Ioi
  have h2 : ({x : ℝ | c < x} : Set ℝ) = (Set.Iic c)ᶜ := by
    ext x
    simp
  rw [h1, h2, probReal_compl_eq_one_sub measurableSet_Iic, ← cdf_eq_real ν c]
  linarith

/-- Corollary: rounding the cutoff upward keeps the level. -/
theorem measureReal_lt_le_of_le_cdf_mono {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {T : Ω → ℝ} (hT : HasLaw T ν P) {α c c' : ℝ}
    (hle : c ≤ c') (hc : 1 - α ≤ cdf ν c) : P.real {ω | c' < T ω} ≤ α := by
  exact measureReal_lt_le_of_le_cdf hT (le_trans hc (monotone_cdf ν hle))

end MathlibExt.Probability.Statistics
