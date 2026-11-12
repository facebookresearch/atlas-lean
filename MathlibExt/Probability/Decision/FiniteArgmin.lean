/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Decision.BayesEstimator

/-!
# Measurable Bayes actions over a finite action space

Mathlib's `ProbabilityTheory.HasArgminEstimator ℓ P π` asserts that the minimizer of the posterior
expected loss `y ↦ ∫⁻ θ, ℓ θ y ∂(P†π) x` can be chosen measurably in the observation `x`. Mathlib
leaves its general existence to future measurable-selection theory. This file proves it when the
action space is finite and nonempty, picking the first minimizer in an enumeration, and derives
the Bayes-risk formula from `HasArgminEstimator.bayesRisk_eq`.

The action space needs no measurable singletons: the selector is built by `Nat.find` from
constant maps.

The construction generalizes `Cslib.MachineLearning.BayesClassifier.exists_isPosteriorArgmax`
(`CSLibExt/MachineLearning/Generative/BayesClassifier.lean`). That theorem builds the same
first-index selector for the 0-1 loss over finitely many classes, by maximizing the posterior
masses of singletons, and so needs measurable singletons. Here the posterior expected loss of a
general loss is minimized instead.

## Main results

* `ProbabilityTheory.hasArgminEstimator_of_finite`: a measurable argmin estimator exists.
* `ProbabilityTheory.bayesRisk_eq_lintegral_iInf_of_finite`:
  `bayesRisk ℓ P π = ∫⁻ x, ⨅ y, ∫⁻ θ, ℓ θ y ∂(P†π) x ∂(P ∘ₘ π)`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory

/-- **Measurable Bayes actions over a finite action space.** If the action space is finite and
nonempty and each section `θ ↦ ℓ θ y` of the loss is measurable, a measurable minimizer of the
posterior expected loss exists. Ties go to the first minimizer in an enumeration of the
actions. -/
theorem hasArgminEstimator_of_finite
    {Θ 𝓧 𝓨 : Type*} [MeasurableSpace Θ] [MeasurableSpace 𝓧] [MeasurableSpace 𝓨]
    [StandardBorelSpace Θ] [Nonempty Θ] [Finite 𝓨] [Nonempty 𝓨]
    {ℓ : Θ → 𝓨 → ℝ≥0∞} (hℓ : ∀ y, Measurable fun θ => ℓ θ y)
    (P : Kernel Θ 𝓧) [IsFiniteKernel P] (π : Measure Θ) [IsFiniteMeasure π] :
    HasArgminEstimator ℓ P π := by
  classical
  have := Encodable.ofCountable 𝓨
  obtain ⟨c₀⟩ := ‹Nonempty 𝓨›
  let A : 𝓨 → Set 𝓧 := fun y =>
    {x | ∀ y', ∫⁻ θ, ℓ θ y ∂(P†π) x ≤ ∫⁻ θ, ℓ θ y' ∂(P†π) x}
  have hA : ∀ y, MeasurableSet (A y) := fun y => by
    simp only [A, Set.ofPred_forall]
    exact MeasurableSet.iInter fun y' =>
      measurableSet_le (hℓ y).lintegral_kernel (hℓ y').lintegral_kernel
  have hex : ∀ x, ∃ y, x ∈ A y := fun x =>
    (Finite.exists_min fun y => ∫⁻ θ, ℓ θ y ∂(P†π) x).imp fun _ h => h
  let p : ℕ → 𝓧 → Prop := fun n x => ∃ y, Encodable.decode n = some y ∧ x ∈ A y
  have hp : ∀ n, MeasurableSet {x | p n x} := fun n => by
    cases h : (Encodable.decode n : Option 𝓨) with
    | none => simp [p, h]
    | some y => simpa [p, h] using hA y
  have hn : ∀ x, ∃ n, p n x := fun x => by
    obtain ⟨y, hy⟩ := hex x
    exact ⟨Encodable.encode y, y, Encodable.encodek y, hy⟩
  let g : ℕ → 𝓧 → 𝓨 := fun n _ => (Encodable.decode n).getD c₀
  refine ⟨⟨fun x => g (Nat.find (hn x)) x,
    ⟨Measurable.find (f := g) (fun _ => measurable_const) hp hn, ae_of_all _ fun x => ?_⟩⟩⟩
  obtain ⟨y, hdec, hy⟩ := Nat.find_spec (hn x)
  simp only [g, hdec, Option.getD_some]
  exact le_antisymm (le_iInf hy) (iInf_le _ y)

/-- Over a finite nonempty action space, the Bayes risk equals the integral, over the marginal law
of the data, of the smallest posterior expected loss. -/
theorem bayesRisk_eq_lintegral_iInf_of_finite
    {Θ 𝓧 𝓨 : Type*} [MeasurableSpace Θ] [MeasurableSpace 𝓧] [MeasurableSpace 𝓨]
    [StandardBorelSpace Θ] [Nonempty Θ] [Finite 𝓨] [Nonempty 𝓨]
    {ℓ : Θ → 𝓨 → ℝ≥0∞} (hl : Measurable (Function.uncurry ℓ))
    (P : Kernel Θ 𝓧) [IsFiniteKernel P] (π : Measure Θ) [IsFiniteMeasure π] :
    bayesRisk ℓ P π = ∫⁻ x, ⨅ y, ∫⁻ θ, ℓ θ y ∂((P†π) x) ∂(P ∘ₘ π) := by
  exact (hasArgminEstimator_of_finite (fun _ => hl.of_uncurry_right) P π).bayesRisk_eq hl

end ProbabilityTheory
