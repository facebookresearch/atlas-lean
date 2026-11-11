/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.WrightFisherChainConstruction

/-!
# Tests of the finite-chain bridge for the canonical Markov law

Fixtures use the existing canonical measure rather than a second path-law definition.
The Wright–Fisher interior fixture is random; the two-state flip is deterministic
but nonconstant. The probability instance comes from the existing construction.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open MathlibExt.Probability.FiniteMarkovChain
open MathlibExt.Probability.MarkovChainConstruction
open MathlibExt.Biology.PopulationGenetics.WrightFisherChain

namespace MathlibExtTest.Probability.FiniteMarkovChainConstruction

example {M : ℕ} (P : StochasticMatrix M) (i : Fin (M + 1)) :
    ∃ μ : Measure (ℕ → Fin (M + 1)), IsProbabilityMeasure μ ∧
      IsFiniteMarkovChain (fun n ω ↦ ω n) P Filtration.piLE μ ∧
      (∀ᵐ ω ∂μ, ω 0 = i) := by
  refine ⟨markovChainMeasure (finiteChainKernel P) (Measure.dirac i), inferInstance, ?_, ?_⟩
  · exact isFiniteMarkovChain_markovChainMeasure P i
  · exact ae_eval_zero_markovChainMeasure P i

example {M : ℕ} (P : StochasticMatrix M) (i : Fin (M + 1)) :
    (markovChainMeasure (finiteChainKernel P) (Measure.dirac i)).map
      (fun ω ↦ ω 0) = Measure.dirac i :=
  markovChainMeasure_initial_distribution (finiteChainKernel P) (Measure.dirac i)

private theorem map_eval_one {M : ℕ} (P : StochasticMatrix M) (i : Fin (M + 1)) :
    (markovChainMeasure (finiteChainKernel P) (Measure.dirac i)).map
      (fun ω ↦ ω 1) = finiteChainKernel P i := by
  have h := (isFiniteMarkovChain_markovChainMeasure P i).map_succ_eq_bind 0
  rw [markovChainMeasure_initial_distribution] at h
  exact h.trans (Measure.dirac_bind (finiteChainKernel P).measurable i)

private theorem firstStepReal {M : ℕ} (P : StochasticMatrix M)
    (i j : Fin (M + 1)) :
    (markovChainMeasure (finiteChainKernel P) (Measure.dirac i)).real
      {ω | ω 1 = j} = P.prob i j := by
  have hm : Measurable (fun ω : ℕ → Fin (M + 1) ↦ ω 1) := measurable_pi_apply 1
  have hmass : (markovChainMeasure (finiteChainKernel P) (Measure.dirac i))
      {ω | ω 1 = j} = ENNReal.ofReal (P.prob i j) := by
    calc
      (markovChainMeasure (finiteChainKernel P) (Measure.dirac i)) {ω | ω 1 = j} =
          ((markovChainMeasure (finiteChainKernel P) (Measure.dirac i)).map
            (fun ω ↦ ω 1)) {j} :=
        (Measure.map_apply hm (measurableSet_singleton j)).symm
      _ = ENNReal.ofReal (P.prob i j) := by
        rw [map_eval_one]
        simpa using finiteChainKernel_apply P i ({j} : Finset (Fin (M + 1)))
  rw [measureReal_def, hmass, ENNReal.toReal_ofReal (P.nonneg i j)]

example :
    (markovChainMeasure (finiteChainKernel (wrightFisher 2)) (Measure.dirac (1 : Fin 3))).real
      {ω | ω 1 = 0} = (1 / 4 : ℝ) := by
  rw [firstStepReal]
  norm_num [wrightFisher_prob, coe_z]

example :
    (markovChainMeasure (finiteChainKernel (wrightFisher 2)) (Measure.dirac (1 : Fin 3))).real
      {ω | ω 1 = 1} = (1 / 2 : ℝ) := by
  rw [firstStepReal]
  norm_num [wrightFisher_prob, coe_z]

example :
    (markovChainMeasure (finiteChainKernel (wrightFisher 2)) (Measure.dirac (1 : Fin 3))).real
      {ω | ω 1 = 2} = (1 / 4 : ℝ) := by
  rw [firstStepReal]
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

/-- The two-state deterministic flip, not an absorbing or constant chain. -/
private def flipMatrix : StochasticMatrix 1 where
  prob i j := if i = j then 0 else 1
  nonneg i j := by split_ifs <;> norm_num
  row_sum i := by fin_cases i <;> rw [Fin.sum_univ_two] <;> norm_num

example :
    (markovChainMeasure (finiteChainKernel flipMatrix) (Measure.dirac (0 : Fin 2))).real
      {ω | ω 1 = 1} = 1 := by
  rw [firstStepReal]
  norm_num [flipMatrix]

example :
    (markovChainMeasure (finiteChainKernel flipMatrix) (Measure.dirac (1 : Fin 2))).real
      {ω | ω 1 = 0} = 1 := by
  rw [firstStepReal]
  norm_num [flipMatrix]

end MathlibExtTest.Probability.FiniteMarkovChainConstruction
