/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Distributions.PoissonKernel
public import MathlibExt.Probability.WaldEquation

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic.Linarith

/-! # Annual loss from a Poisson occurrence model -/

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

@[expose] public section

/-- **Annual loss from a Poisson occurrence model.** Let `N` be the one-year event count with
Poisson mean `lam`, and let `L i` be identically distributed real losses with integrable `L 0`.
Each loss is independent of the count. The year’s total loss is the sum of the first `N` losses
(with indices starting at zero). It is integrable and its mean is `lam` times the mean of `L 0`.
The probability of a positive count is `1 - exp (-lam)`, at most `lam`. Mutual independence of
the losses is not needed for these conclusions. Grinstead and Snell, *Introduction to Probability*,
§5.1, gives the Poisson count law; the total-loss identity uses Wald’s equation. -/
theorem annual_poisson_loss {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (lam : ℝ≥0) (N : Ω → ℕ) (L : ℕ → Ω → ℝ)
    (hNmeas : Measurable N) (hN : HasLaw N (poissonMeasure lam) P)
    (hLlaw : ∀ i j, IdentDistrib (L i) (L j) P P) (hL : Integrable (L 0) P)
    (hIndep : ∀ i, IndepFun (L i) N P) :
    let A := fun ω => ∑ i ∈ Finset.range (N ω), L i ω
    Integrable A P ∧
      (∫ ω, A ω ∂P) = (lam : ℝ) * (∫ ω, L 0 ω ∂P) ∧
      P.real {ω | 0 < N ω} = 1 - Real.exp (-(lam : ℝ)) ∧
      P.real {ω | 0 < N ω} ≤ lam := by
  intro A
  let f : Filtration ℕ (inferInstance : MeasurableSpace Ω) :=
    Filtration.const ℕ (MeasurableSpace.comap N inferInstance) hNmeas.comap_le
  have hStop : IsStoppingTime f (fun ω => (N ω : WithTop ℕ)) := by
    intro k
    change MeasurableSet[MeasurableSpace.comap N inferInstance] {ω | (N ω : WithTop ℕ) ≤ k}
    exact ⟨{n : ℕ | (n : WithTop ℕ) ≤ k}, MeasurableSet.of_discrete, rfl⟩
  have hIndepF (i : ℕ) : Indep (MeasurableSpace.comap (L i) inferInstance) (f i) P :=
    hIndep i
  have hCountInt : Integrable (fun ω => (N ω : ℝ)) P :=
    hN.integrable_comp (integrable_natCast_poissonMeasure lam)
  have hCountMean : (∫ ω, (N ω : ℝ) ∂P) = lam := by
    simpa only [Function.comp_def, integral_natCast_poissonMeasure] using
      hN.integral_comp (integrable_natCast_poissonMeasure lam).aestronglyMeasurable
  have hZero : P.real {ω | N ω = 0} = Real.exp (-(lam : ℝ)) := by
    rw [hN.measureReal_eq (p := fun n => n = 0) (measurableSet_singleton (0 : ℕ))]
    change (poissonMeasure lam).real {0} = _
    rw [poissonMeasure_real_singleton]
    simp
  have hEvent : P.real {ω | 0 < N ω} = 1 - Real.exp (-(lam : ℝ)) := by
    have hset : {ω | 0 < N ω} = {ω | N ω = 0}ᶜ := by
      ext ω
      exact Nat.pos_iff_ne_zero
    have hmeasZero : MeasurableSet {ω | N ω = 0} :=
      hNmeas (measurableSet_singleton (0 : ℕ))
    rw [hset, probReal_compl_eq_one_sub hmeasZero, hZero]
  refine ⟨wald_integrable_stopped_sum hLlaw hL hStop hIndepF hCountInt, ?_, hEvent, ?_⟩
  · change (∫ ω, ∑ i ∈ Finset.range (N ω), L i ω ∂P) = _
    rw [wald_equation hLlaw hL hStop hIndepF hCountInt, hCountMean, mul_comm]
  · rw [hEvent]
    linarith [Real.add_one_le_exp (-(lam : ℝ))]

end

end ProbabilityTheory
