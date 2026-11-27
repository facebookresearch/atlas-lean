/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.FiniteMarkovChainConstruction

/-!
# Tests of the finite-chain bridge for the canonical Markov law

Fixtures use the existing canonical measure rather than a second path-law definition.
The two-state flip is deterministic but nonconstant.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open MathlibExt.Probability.FiniteMarkovChain
open MathlibExt.Probability.MarkovChainConstruction

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
