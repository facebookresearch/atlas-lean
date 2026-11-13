/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Experiment.Identification

open MeasureTheory Finset
open MathlibExt.Probability.Causality
open MathlibExt.Probability.Statistics
open MathlibExt.Probability.Statistics.Experiment
open MathlibExt.Probability.Statistics.Experiment.Identification

namespace MathlibExtTest.Probability.Statistics.Experiment.Identification

/-- Use case (duplicate labels allowed): labeled schedules with the label ignored
satisfy identification through the target theorem, so identification does not
require injectivity of the parameter-to-law map. -/
example {ι : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace ι] [DiscreteMeasurableSpace ι]
    {n₁ : ℕ} (h₁ : 1 ≤ n₁) (h₀ : n₁ + 1 ≤ Fintype.card ι) :
    IsIdentifiedBy
      (fun θ : ((ι → ℝ) × (ι → ℝ)) × ℕ =>
        obsLaw ((Measure.uniformOfFinset Finset.univ).prod (completeRandomization ι n₁))
          {p : ι × Finset ι | p.1 ∈ p.2} Prod.fst
          (fun p => θ.1.1 p.1) (fun p => θ.1.2 p.1))
      (fun θ : ((ι → ℝ) × (ι → ℝ)) × ℕ => ate θ.1.1 θ.1.2) := by
  intro θ θ' h
  exact ate_isIdentifiedBy_completeRandomization h₁ h₀ θ.1 θ'.1 h

/-- Counterexample (bare law): the outcome-independent complete-randomization law
does not identify the ATE. On `Fin 2` with `n₁ = 1`, the all-zero schedule has
ATE `0` while the schedule with `y₀ = 0` and `y₁ i = (i.val : ℝ)` has ATE
`1 / 2`, under the same treated-set law. -/
example :
    ¬ IsIdentifiedBy
      (fun _ : ((Fin 2 → ℝ) × (Fin 2 → ℝ)) => completeRandomization (Fin 2) 1)
      (fun θ : (Fin 2 → ℝ) × (Fin 2 → ℝ) => ate θ.1 θ.2) := by
  apply not_isIdentifiedBy_of_eq_of_ne (θ := ((fun _ => 0), (fun _ => 0)))
    (θ' := ((fun _ => 0), (fun i => (i.val : ℝ)))) rfl
  simp only [ate, popMean]
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  simp

end MathlibExtTest.Probability.Statistics.Experiment.Identification
