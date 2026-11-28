/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.GraphicalModels.HammersleyClifford
public import Mathlib.Data.Fin.VecNotation

/-!
# Tests for Hammersley–Clifford

The four-cycle witness is pairwise Markov but not Gibbs and not strictly
positive; the constant positive weight on the same graph does factorize, and
the positive pairwise/Gibbs equivalence applies to it.
-/

@[expose] public section

namespace Cslib.MachineLearning.GraphicalModels.HammersleyCliffordTest

open Cslib.MachineLearning.GraphicalModels

theorem fourCycle_support_one :
    fourCycleWeight ![true, true, false, false] = 1 := by
  simp [fourCycleWeight]

theorem fourCycle_zero_off_support :
    fourCycleWeight ![false, false, false, false] = 0 := by
  simp [fourCycleWeight]

theorem fourCycle_pairwise_not_gibbs :
    PairwiseMarkov fourCycleGraph fourCycleWeight ∧
      ¬ GibbsFactorization fourCycleGraph fourCycleWeight :=
  ⟨fourCycleWeight_pairwiseMarkov, fourCycleWeight_not_gibbsFactorization⟩

theorem fourCycle_witness_not_positive :
    ¬ ∀ x, 0 < fourCycleWeight x :=
  fourCycleWeight_not_pos

/-- The constant weight `1` on the four-cycle Gibbs-factorizes (empty family). -/
theorem fourCycle_gibbsFactorization_one :
    GibbsFactorization fourCycleGraph (fun _ : Fin 4 → Bool => 1) := by
  refine ⟨∅, fun _ _ => 1, by simp, by simp, by simp, by simp⟩

/-- Hence, by the positive equivalence, it is pairwise Markov. -/
theorem fourCycle_one_pairwiseMarkov :
    PairwiseMarkov fourCycleGraph (fun _ : Fin 4 → Bool => 1) := by
  have hp : ∀ x : Fin 4 → Bool, 0 < (fun _ : Fin 4 → Bool => (1 : ℝ)) x := by
    intro x
    norm_num
  exact (gibbsFactorization_iff_pairwiseMarkov_of_pos hp).mp
    fourCycle_gibbsFactorization_one

/-- And every strictly positive pairwise-Markov weight on the four-cycle
factorizes over its cliques. -/
theorem fourCycle_positive_pairwise_gibbs {p : (Fin 4 → Bool) → ℝ}
    (hp : ∀ x, 0 < p x) (h : PairwiseMarkov fourCycleGraph p) :
    GibbsFactorization fourCycleGraph p :=
  gibbsFactorization_of_pairwiseMarkov_of_pos hp h

end Cslib.MachineLearning.GraphicalModels.HammersleyCliffordTest
