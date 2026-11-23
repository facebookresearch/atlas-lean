/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Sufficiency.Basic
public import MathlibExt.Probability.Statistics.Sufficiency.Discrete
public import MathlibExt.Probability.Statistics.Sufficiency.RaoBlackwell

/-!
# Discrete sufficiency is σ-algebra sufficiency

On a finite observation space with the discrete σ-algebra, a statistic `T` that is sufficient
for a family of mass functions (`IsSufficientPMF`) generates a sufficient σ-algebra
(`IsSufficient`) for the corresponding probability measures. This connects the discrete
Fisher–Neyman factorization theorem to the measure-theoretic sufficiency layer used by the
Rao–Blackwell theorem.

## Main results

* `IsSufficientPMF.isSufficient_comap`
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

namespace MathlibExt.Probability.Statistics.Sufficiency

set_option linter.unusedFintypeInType false in
/-- **Discrete sufficiency is σ-algebra sufficiency.** On a finite observation space with the
discrete σ-algebra, a statistic `T` that is sufficient for the mass functions `P θ` generates a
sufficient σ-algebra `comap T` for the probability measures `(P θ).toMeasure`. -/
theorem IsSufficientPMF.isSufficient_comap {Θ X τ : Type*} [Fintype X] [MeasurableSpace X]
    [DiscreteMeasurableSpace X] [MeasurableSpace τ] [DiscreteMeasurableSpace τ]
    {P : Θ → PMF X} {T : X → τ} (hT : IsSufficientPMF P T) :
    IsSufficient (MeasurableSpace.comap T ‹MeasurableSpace τ›) fun θ => (P θ).toMeasure := by
  obtain ⟨h, -, hfac⟩ := hT.factorization
  have : IsFiniteMeasure ((Measure.count : Measure X).withDensity fun x => (h x : ℝ≥0∞)) :=
    isFiniteMeasure_withDensity (by
      rw [lintegral_fintype]
      exact ENNReal.sum_ne_top.mpr fun x _ =>
        ENNReal.mul_ne_top ENNReal.coe_ne_top (measure_ne_top _ _))
  refine isSufficient_comap_of_factorization_of_sigmaFinite_trim Measurable.of_discrete
    Measure.count (fun θ t => (P θ).map T t) (fun _ => Measurable.of_discrete)
    (fun x => (h x : ℝ≥0∞)) Measurable.of_discrete
    fun θ => Measure.ext_of_singleton fun x => ?_
  rw [PMF.toMeasure_apply_singleton _ _ MeasurableSet.of_discrete,
    withDensity_apply _ MeasurableSet.of_discrete, lintegral_singleton, Measure.count_singleton,
    mul_one, hfac]

set_option linter.unusedFintypeInType false in
/-- **Rao–Blackwell through the discrete bridge.** Composing the discrete-to-σ-algebra
bridge with the comap Rao–Blackwell theorem gives the squared-risk split for a sufficient
statistic of mass functions. -/
theorem IsSufficientPMF.raoBlackwell_comap_sq
    {Θ X τ : Type*} [Fintype X] [MeasurableSpace X] [DiscreteMeasurableSpace X]
    [MeasurableSpace τ] [DiscreteMeasurableSpace τ]
    {P : Θ → PMF X} {T : X → τ} (hT : IsSufficientPMF P T)
    {W : X → ℝ} (hW : ∀ θ, MemLp W 2 (P θ).toMeasure) (tgt : Θ → ℝ) :
    ∃ φ : τ → ℝ, Measurable φ ∧
      ∀ θ, ∫ ω, (W ω - tgt θ) ^ 2 ∂(P θ).toMeasure =
        ∫ ω, (φ (T ω) - tgt θ) ^ 2 ∂(P θ).toMeasure +
        ∫ ω, (W ω - φ (T ω)) ^ 2 ∂(P θ).toMeasure := by
  obtain ⟨φ, hφ, -, -, hpyth⟩ :=
    raoBlackwell_comap Measurable.of_discrete hT.isSufficient_comap
      Measurable.of_discrete hW tgt
  exact ⟨φ, hφ, hpyth⟩

end MathlibExt.Probability.Statistics.Sufficiency
