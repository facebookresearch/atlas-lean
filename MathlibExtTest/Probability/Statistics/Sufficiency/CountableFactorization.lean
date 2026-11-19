/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Sufficiency.CountableFactorization

@[expose] public section

namespace MathlibExtTest.Probability.Statistics.Sufficiency.CountableFactorization

open MeasureTheory

open scoped ENNReal NNReal

/-- Fixture A (through the main theorem): the two-point Bernoulli family factors. The
ambient `MeasurableSpace Bool` instance is the canonical one (verified by `#check
inferInstance` against Mathlib at the pin); no explicit `m₀` binder is used. -/
example (μ : Measure Bool) [SigmaFinite μ]
    (P : Bool → Measure Bool) [∀ θ, IsProbabilityMeasure (P θ)]
    (hdom : ∀ θ, P θ ≪ μ)
    (hP : MathlibExt.Probability.Statistics.Sufficiency.IsSufficient (MeasurableSpace.comap (id : Bool → Bool) inferInstance) P) :
    ∃ (g : Bool → Bool → ℝ≥0∞) (h : Bool → ℝ≥0∞), (∀ θ, Measurable (g θ)) ∧
      Measurable h ∧
      ∀ θ, P θ = μ.withDensity (fun ω => g θ ((id : Bool → Bool) ω) * h ω) := by
  exact MathlibExt.Probability.Statistics.Sufficiency.exists_factorization_of_isSufficient_comap_countable
    measurable_id μ P hdom hP

/-- Fixture B (boundary): a singleton family factors trivially. -/
example (μ : Measure Bool) [SigmaFinite μ]
    (P : Unit → Measure Bool) [∀ θ, IsProbabilityMeasure (P θ)]
    (hdom : ∀ θ, P θ ≪ μ)
    (hP : MathlibExt.Probability.Statistics.Sufficiency.IsSufficient (MeasurableSpace.comap (id : Bool → Bool) inferInstance) P) :
    ∃ (g : Unit → Bool → ℝ≥0∞) (h : Bool → ℝ≥0∞), (∀ θ, Measurable (g θ)) ∧
      Measurable h ∧
      ∀ θ, P θ = μ.withDensity (fun ω => g θ ((id : Bool → Bool) ω) * h ω) := by
  exact MathlibExt.Probability.Statistics.Sufficiency.exists_factorization_of_isSufficient_comap_countable
    measurable_id μ P hdom hP

/-- Fixture C (non-vacuity): an explicit satisfiable family — two Dirac masses against
counting measure. Prove the domination and the identity-sufficiency from discreteness
(`Measurable.of_discrete`, counting-measure singleton masses), then apply the main
theorem; the resulting factorization has θ-independent `h`. -/
example (P : Bool → Measure Bool) [∀ θ, IsProbabilityMeasure (P θ)]
    (hPdens : ∀ θ, P θ = Measure.count.withDensity (fun ω => if ω = θ then 1 else 0)) :
    ∃ (g : Bool → Bool → ℝ≥0∞) (h : Bool → ℝ≥0∞), (∀ θ, Measurable (g θ)) ∧
      Measurable h ∧
      ∀ θ, P θ =
        Measure.count.withDensity (fun ω => g θ ((id : Bool → Bool) ω) * h ω) := by
  have hdom : ∀ θ, P θ ≪ Measure.count := by
    intro θ
    rw [hPdens θ]
    exact withDensity_absolutelyContinuous _ _
  have hP : MathlibExt.Probability.Statistics.Sufficiency.IsSufficient
      (MeasurableSpace.comap (id : Bool → Bool) inferInstance) P := by
    rw [MeasurableSpace.comap_id]
    refine ⟨le_rfl, fun θ => inferInstance, fun s hs => ?_⟩
    refine ⟨s.indicator (fun _ => (1 : ℝ)),
      (measurable_const.indicator hs).stronglyMeasurable, fun θ => ?_⟩
    have hfm : StronglyMeasurable (s.indicator (fun _ => (1 : ℝ))) :=
      (measurable_const.indicator hs).stronglyMeasurable
    have hfi : Integrable (s.indicator (fun _ => (1 : ℝ))) (P θ) :=
      (integrable_const (1 : ℝ)).indicator hs
    have heq : (P θ)[s.indicator (fun _ => (1 : ℝ)) | inferInstance]
        = s.indicator (fun _ => (1 : ℝ)) :=
      condExp_of_stronglyMeasurable le_rfl hfm hfi
    rw [heq]
  exact MathlibExt.Probability.Statistics.Sufficiency.exists_factorization_of_isSufficient_comap_countable
    measurable_id Measure.count P hdom hP

end MathlibExtTest.Probability.Statistics.Sufficiency.CountableFactorization
