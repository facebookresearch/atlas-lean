/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.PopulationGenetics.WrightFisherChainConstruction

/-! The Wright–Fisher chain: interior transitions, fixation, and the zero-size case. -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open MathlibExt.Probability.FiniteMarkovChain
open MathlibExt.Probability.MarkovChainConstruction
open MathlibExt.Biology.PopulationGenetics.WrightFisherChain

namespace MathlibExtTest.Probability.FiniteMarkovChainConstruction

/-- The first generation from the interior state has the binomial row of the population kernel. -/
private theorem firstGeneration (j : Fin 3) :
    (markovChainMeasure (finiteChainKernel (wrightFisher 2)) (Measure.dirac (1 : Fin 3))).real
      {ω | ω 1 = j} = (wrightFisher 2).prob 1 j := by
  let P := wrightFisher 2
  have h := (isFiniteMarkovChain_markovChainMeasure P 1).toIsMarkovChain.map_eq_bind_pow 0 1
  simp only [zero_add, pow_one, markovChainMeasure_initial_distribution,
    Measure.dirac_bind (finiteChainKernel P).measurable] at h
  change (markovChainMeasure (finiteChainKernel P) (Measure.dirac 1)).real
    ((fun ω : ℕ → Fin 3 ↦ ω 1) ⁻¹' {j}) = P.prob 1 j
  rw [← map_measureReal_apply (measurable_pi_apply 1) (measurableSet_singleton j), h]
  simpa [measureReal_def, (P.nonneg 1 j)] using
    congrArg ENNReal.toReal (finiteChainKernel_apply P 1 {j})

example :
    (markovChainMeasure (finiteChainKernel (wrightFisher 2)) (Measure.dirac (1 : Fin 3))).real
      {ω | ω 1 = 0} = (1 / 4 : ℝ) := by
  rw [firstGeneration]
  norm_num [wrightFisher_prob, coe_z]

example :
    (markovChainMeasure (finiteChainKernel (wrightFisher 2)) (Measure.dirac (1 : Fin 3))).real
      {ω | ω 1 = 1} = (1 / 2 : ℝ) := by
  rw [firstGeneration]
  norm_num [wrightFisher_prob, coe_z]

example :
    (markovChainMeasure (finiteChainKernel (wrightFisher 2)) (Measure.dirac (1 : Fin 3))).real
      {ω | ω 1 = 2} = (1 / 4 : ℝ) := by
  rw [firstGeneration]
  norm_num [wrightFisher_prob, coe_z]

example :
    IsFiniteMarkovChain (fun n (ω : ℕ → Fin 3) ↦ ω n) (wrightFisher 2) Filtration.piLE
      (markovChainMeasure (finiteChainKernel (wrightFisher 2)) (Measure.dirac 1)) :=
  isFiniteMarkovChain_markovChainMeasure (wrightFisher 2) 1

example :
    (markovChainMeasure (finiteChainKernel (wrightFisher 2)) (Measure.dirac (1 : Fin 3)))
      {ω | ∃ t, ω t = 0 ∨ ω t = Fin.last 2} = 1 :=
  measure_markovChainMeasure_exists_absorbed 2 1

example :
    (markovChainMeasure (finiteChainKernel (wrightFisher 2)) (Measure.dirac (1 : Fin 3))).real
      {ω | ∃ t, ω t = Fin.last 2} = (1 / 2 : ℝ) := by
  simpa using measureReal_markovChainMeasure_exists_eq_last
    (M := 2) (by norm_num) (1 : Fin 3)

example :
    (markovChainMeasure (finiteChainKernel (wrightFisher 2)) (Measure.dirac (1 : Fin 3))).real
      {ω | ∃ t, ω t = 0} = (1 / 2 : ℝ) := by
  have h := measureReal_markovChainMeasure_exists_eq_zero (M := 2) (by norm_num) (1 : Fin 3)
  norm_num at h
  exact h

example :
    (markovChainMeasure (finiteChainKernel (wrightFisher 0)) (Measure.dirac 0)).real
      {ω | ∀ n, ω n = 0} = 1 := by
  have h : {ω : ℕ → Fin 1 | ∀ n, ω n = 0} = Set.univ :=
    Set.eq_univ_of_forall fun ω n ↦ Subsingleton.elim (ω n) 0
  rw [h]
  simp

end MathlibExtTest.Probability.FiniteMarkovChainConstruction
