/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.Probability.Kernel.Basic

/-!
# Estimand identification and the two-point lower bound

A real estimand `τ` is identified by observation laws `P` when parameters with equal laws have
equal estimand values (`IsIdentifiedBy`); this is weaker than injectivity of `θ ↦ P θ`. If two
parameters have the same law but estimand values more than `2ε` apart, no fixed measurable
estimator can be within `ε` of the estimand with probability above `1/2` at both: identification
is necessary for accurate estimation, but it is not itself a statement about any estimator.

## Main definitions

* `IsIdentifiedBy`

## Main results

* `two_point_lower_bound`: the two `ε`-success probabilities sum to at most `1`.
* `exists_measureReal_failure_ge_half`: one failure probability is at least `1/2`.
* `not_isIdentifiedBy_of_eq_of_ne`: equal laws with different estimand values refute
  identification.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace MathlibExt.Probability.Statistics

/-- The real estimand `τ` is *identified* by the family of observation laws `P` if parameters
with equal laws have equal estimand values. This is weaker than injectivity of `θ ↦ P θ`. -/
def IsIdentifiedBy {Θ X : Type*} [MeasurableSpace X] (P : Θ → Measure X) (τ : Θ → ℝ) : Prop :=
  ∀ θ θ', P θ = P θ' → τ θ = τ θ'

set_option linter.unusedVariables false in
/-- **Two-point indistinguishability.** If two parameters have the same observation law and
estimand values more than `2ε` apart, the `ε`-success events of any fixed measurable estimator
`δ` at the two parameters have total probability at most `1`. -/
theorem two_point_lower_bound {Θ X : Type*} [MeasurableSpace X]
    (P : Θ → Measure X) (τ : Θ → ℝ) {θ θ' : Θ} (hP : P θ = P θ')
    [IsProbabilityMeasure (P θ)] {δ : X → ℝ} (hδ : Measurable δ) {ε : ℝ} (hε : 0 ≤ ε)
    (hsep : 2 * ε < |τ θ - τ θ'|) :
    (P θ).real {x | |δ x - τ θ| ≤ ε} + (P θ').real {x | |δ x - τ θ'| ≤ ε} ≤ 1 := by
  rw [← hP]
  have hdisj : Disjoint {x | |δ x - τ θ| ≤ ε} {x | |δ x - τ θ'| ≤ ε} :=
    Set.disjoint_left.2 fun x (h1 : |δ x - τ θ| ≤ ε) (h2 : |δ x - τ θ'| ≤ ε) => by
      linarith [abs_sub_le (τ θ) (δ x) (τ θ'), abs_sub_comm (τ θ) (δ x)]
  have hm : MeasurableSet {x | |δ x - τ θ'| ≤ ε} :=
    measurableSet_le (continuous_abs.measurable.comp (hδ.sub_const _)) measurable_const
  rw [← measureReal_union hdisj hm]
  exact measureReal_le_one

/-- **Estimation lower bound from non-identification.** Under the same hypotheses, every fixed
measurable estimator misses the estimand by more than `ε` with probability at least `1/2` at
one of the two parameters. -/
theorem exists_measureReal_failure_ge_half {Θ X : Type*} [MeasurableSpace X]
    (P : Θ → Measure X) (τ : Θ → ℝ) {θ θ' : Θ} (hP : P θ = P θ')
    [IsProbabilityMeasure (P θ)] {δ : X → ℝ} (hδ : Measurable δ) {ε : ℝ} (hε : 0 ≤ ε)
    (hsep : 2 * ε < |τ θ - τ θ'|) :
    1 / 2 ≤ (P θ).real {x | ε < |δ x - τ θ|} ∨ 1 / 2 ≤ (P θ').real {x | ε < |δ x - τ θ'|} := by
  have h := two_point_lower_bound P τ hP hδ hε hsep
  have hc : ∀ c : ℝ, {x | ε < |δ x - c|} = {x | |δ x - c| ≤ ε}ᶜ := fun c => by
    ext x
    simp [not_le]
  have hm : ∀ c : ℝ, MeasurableSet {x | |δ x - c| ≤ ε} := fun c =>
    measurableSet_le (continuous_abs.measurable.comp (hδ.sub_const _)) measurable_const
  rw [← hP] at h ⊢
  rw [hc, hc, probReal_compl_eq_one_sub (hm _), probReal_compl_eq_one_sub (hm _)]
  by_contra hne
  rw [not_or, not_le, not_le] at hne
  linarith [hne.1, hne.2]

/-- Equal laws with different estimand values refute identification. -/
theorem not_isIdentifiedBy_of_eq_of_ne {Θ X : Type*} [MeasurableSpace X]
    {P : Θ → Measure X} {τ : Θ → ℝ} {θ θ' : Θ} (hP : P θ = P θ') (hτ : τ θ ≠ τ θ') :
    ¬ IsIdentifiedBy P τ := by
  exact fun h => hτ (h θ θ' hP)

/-- **Two-point bound for randomized rules.** Equal observation laws induce equal output
laws under a fixed Markov kernel, so the deterministic disjointness argument applies on
the output space. -/
theorem exists_measureReal_failure_ge_half_kernel {Θ X : Type*} [MeasurableSpace X]
    (P : Θ → Measure X) (τ : Θ → ℝ) {θ θ' : Θ} (hP : P θ = P θ')
    [IsProbabilityMeasure (P θ)] {κ : Kernel X ℝ} [IsMarkovKernel κ]
    {ε : ℝ} (hε : 0 ≤ ε) (hsep : 2 * ε < |τ θ - τ θ'|) :
    1 / 2 ≤ ((P θ).bind κ).real {y | ε < |y - τ θ|} ∨
      1 / 2 ≤ ((P θ').bind κ).real {y | ε < |y - τ θ'|} := by
  have hbind : (P θ).bind κ = (P θ').bind κ := by rw [hP]
  haveI : IsProbabilityMeasure ((P θ).bind κ) := ⟨by
    rw [Measure.bind_apply MeasurableSet.univ (Kernel.measurable κ).aemeasurable]
    have h1 : ∀ a, (κ a : Measure ℝ) Set.univ = 1 :=
      fun a => @measure_univ _ _ _ (IsMarkovKernel.isProbabilityMeasure a)
    simp_rw [h1, lintegral_const, measure_univ, mul_one]
  ⟩
  have hdisj : Disjoint {y | |y - τ θ| ≤ ε} {y | |y - τ θ'| ≤ ε} :=
    Set.disjoint_left.2 fun y (h1 : |y - τ θ| ≤ ε) (h2 : |y - τ θ'| ≤ ε) => by
      linarith [abs_sub_le (τ θ) y (τ θ'), abs_sub_comm (τ θ) y]
  have hm : ∀ c : ℝ, MeasurableSet {y | |y - c| ≤ ε} := fun c =>
    measurableSet_le (continuous_abs.measurable.comp (measurable_id.sub_const _)) measurable_const
  have hsum : ((P θ).bind κ).real {y | |y - τ θ| ≤ ε}
      + ((P θ').bind κ).real {y | |y - τ θ'| ≤ ε} ≤ 1 := by
    rw [← hbind]
    rw [← measureReal_union hdisj (hm _)]
    exact measureReal_le_one
  have hc : ∀ c : ℝ, {y | ε < |y - c|} = {y | |y - c| ≤ ε}ᶜ := fun c => by
    ext y
    simp [not_le]
  rw [← hP] at hsum ⊢
  rw [hc, hc, probReal_compl_eq_one_sub (hm _), probReal_compl_eq_one_sub (hm _)]
  by_contra hne
  rw [not_or, not_le, not_le] at hne
  linarith [hne.1, hne.2]

/-- **Deterministic estimators are the special case.** With `κ := Kernel.deterministic δ`,
the kernel bound is the deterministic bound; the proof is one invocation, not a new
disjointness argument. -/
theorem exists_measureReal_failure_ge_half_of_deterministic {Θ X : Type*} [MeasurableSpace X]
    (P : Θ → Measure X) (τ : Θ → ℝ) {θ θ' : Θ} (hP : P θ = P θ')
    [IsProbabilityMeasure (P θ)] {δ : X → ℝ} (hδ : Measurable δ)
    {ε : ℝ} (hε : 0 ≤ ε) (hsep : 2 * ε < |τ θ - τ θ'|) :
    1 / 2 ≤ ((P θ).bind (Kernel.deterministic δ hδ)).real {y | ε < |y - τ θ|} ∨
      1 / 2 ≤ ((P θ').bind (Kernel.deterministic δ hδ)).real {y | ε < |y - τ θ'|} := by
  haveI := Kernel.isMarkovKernel_deterministic hδ
  exact exists_measureReal_failure_ge_half_kernel (κ := Kernel.deterministic δ hδ)
    P τ hP hε hsep

end MathlibExt.Probability.Statistics
