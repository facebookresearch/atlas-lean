/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.FiniteMarkovChain
public import MathlibExt.Probability.MarkovChainConstruction
import Mathlib.Probability.Process.Adapted

/-!
# Finite-chain specification for the canonical Markov law

The repository already constructs `markovChainMeasure` from a Markov kernel and
initial distribution. This file proves that its matrix-derived, deterministic-initial
specialization satisfies the existing `IsFiniteMarkovChain` predicate.

No new path measure or lifted kernel is defined. The probability instance and initial
marginal come from the canonical construction; regular conditional distributions give
the singleton conditional-probability clause required by the finite specification.
The initial state is an almost-sure property of the law, not every raw sequence.

## References

* O. Kallenberg, *Foundations of Modern Probability*, 3rd ed., Ionescu–Tulcea theorem.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open MathlibExt.Probability.MarkovChainConstruction

namespace MathlibExt.Probability.FiniteMarkovChain

/-- The canonical Markov law with initial distribution `dirac i` starts at `i`
almost surely. Its initial marginal is supplied by the existing construction. -/
theorem ae_eval_zero_markovChainMeasure {M : ℕ} (P : StochasticMatrix M)
    (i : Fin (M + 1)) :
    ∀ᵐ ω ∂markovChainMeasure (finiteChainKernel P) (Measure.dirac i), ω 0 = i := by
  have h : ∀ᵐ j ∂(markovChainMeasure (finiteChainKernel P) (Measure.dirac i)).map
      (fun ω ↦ ω 0), j = i := by
    rw [markovChainMeasure_initial_distribution]
    exact (ae_dirac_iff (measurableSet_singleton i)).mpr rfl
  exact ae_of_ae_map (measurable_pi_apply 0).aemeasurable h

private theorem measurable_eval_piLE {M : ℕ} (n : ℕ) :
    Measurable[Filtration.piLE (X := fun _ : ℕ ↦ Fin (M + 1)) n, _]
      (fun ω : ℕ → Fin (M + 1) ↦ ω n) := by
  rw [Filtration.piLE_eq_comap_frestrictLe]
  exact (measurable_pi_apply (⟨n, Finset.mem_Iic.mpr le_rfl⟩ : Finset.Iic n)).comp
    (comap_measurable (Preorder.frestrictLe n))

private theorem integral_finite_indicator {M : ℕ} (P : StochasticMatrix M)
    (k j : Fin (M + 1)) :
    (∫ y, if y = j then (1 : ℝ) else 0 ∂finiteChainKernel P k) = P.prob k j := by
  have hi : (∫ y, if y = j then (1 : ℝ) else 0 ∂finiteChainKernel P k) =
      (finiteChainKernel P k {j}).toReal := by
    simpa [Set.indicator_apply, Measure.real] using
      (integral_indicator_one (μ := finiteChainKernel P k) (measurableSet_singleton j))
  rw [hi]
  have h := congrArg ENNReal.toReal
    (finiteChainKernel_apply P k ({j} : Finset (Fin (M + 1))))
  simpa [ENNReal.toReal_ofReal (P.nonneg k j)] using h

/-- The coordinate process under the existing canonical matrix-derived Markov law
satisfies the original finite-state Markov-chain specification on `Filtration.piLE`. -/
theorem isFiniteMarkovChain_markovChainMeasure {M : ℕ} (P : StochasticMatrix M)
    (i : Fin (M + 1)) :
    IsFiniteMarkovChain (fun n (ω : ℕ → Fin (M + 1)) ↦ ω n) P Filtration.piLE
      (markovChainMeasure (finiteChainKernel P) (Measure.dirac i)) := by
  let μ := markovChainMeasure (finiteChainKernel P) (Measure.dirac i)
  constructor
  · exact measurable_eval_piLE
  · intro n j
    let f : Fin (M + 1) → ℝ := fun y ↦ if y = j then 1 else 0
    have hf : Measurable f := measurable_of_countable f
    have hY : Measurable (fun ω : ℕ → Fin (M + 1) ↦ ω (n + 1)) :=
      measurable_pi_apply (n + 1)
    have hH : Measurable (Preorder.frestrictLe n :
        (ℕ → Fin (M + 1)) → ((k : Finset.Iic n) → Fin (M + 1))) :=
      Preorder.measurable_frestrictLe n
    have hi : Integrable (fun ω : ℕ → Fin (M + 1) ↦ f (ω (n + 1))) μ := by
      apply Integrable.of_bound (hf.comp hY).aestronglyMeasurable 1
      filter_upwards [] with ω
      dsimp only [f]
      by_cases hω : ω (n + 1) = j <;> simp [hω]
    have he := condExp_ae_eq_integral_condDistrib hH hY.aemeasurable
      hf.stronglyMeasurable hi
    have hd := markovChainMeasure_condDistrib (finiteChainKernel P) (Measure.dirac i) n
    have hd' : ∀ᵐ ω ∂μ,
        condDistrib (fun z : ℕ → Fin (M + 1) ↦ z (n + 1)) (Preorder.frestrictLe n) μ
          (Preorder.frestrictLe n ω) =
            markovLiftKernel (finiteChainKernel P) n (Preorder.frestrictLe n ω) :=
      ae_of_ae_map hH.aemeasurable hd
    change μ[(fun ω ↦ f (ω (n + 1))) | Filtration.piLE n] =ᵐ[μ]
      fun ω ↦ P.prob (ω n) j
    rw [Filtration.piLE_eq_comap_frestrictLe]
    filter_upwards [he, hd'] with ω heω hdω
    rw [hdω] at heω
    change μ[(fun z ↦ f (z (n + 1))) | MeasurableSpace.comap
      (Preorder.frestrictLe n) _] ω =
        ∫ y, f y ∂finiteChainKernel P (ω n) at heω
    exact heω.trans (integral_finite_indicator P (ω n) j)

end MathlibExt.Probability.FiniteMarkovChain
