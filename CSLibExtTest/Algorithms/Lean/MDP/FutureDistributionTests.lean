/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Algorithms.Lean.MDP.FutureDistribution
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! # Regressions for the future-distribution concentration coefficient -/

open scoped Matrix ENNReal
open Convexity Cslib.Algorithms.Lean.MarkovDecision

namespace CSLibExtTest.Algorithms.Lean.MDP.FutureDistribution

-- Action `true` resets to state zero, while `false` flips the state.
private def resetFlip : MDP (Fin 2) Bool ℝ where
  reward := fun _ _ => 0
  prob := fun x a y => if y = (if a then 0 else if x = 0 then 1 else 0) then 1 else 0

private noncomputable def ν : StdSimplex ℝ (Fin 2) := StdSimplex.single 0
private noncomputable def resetThenFlip (i : Fin 2) (_ : Fin 2) : Bool := i == 0
private noncomputable def flipThenReset (i : Fin 2) (_ : Fin 2) : Bool := i == 1

private theorem resetThenFlip_weight : futureStateWeights resetFlip ν 2 resetThenFlip 1 = 1 := by
  norm_num [futureStateWeights, Matrix.vecMul_apply_eq_sum, transitionMatrix, resetFlip, ν,
    resetThenFlip, Fin.sum_univ_two, StdSimplex.weights_single, Finsupp.single_apply]

-- Reversing the two rules changes the destination. These matrices do not commute.
example : futureStateWeights resetFlip ν 2 resetThenFlip 1 = 1 ∧
    futureStateWeights resetFlip ν 2 flipThenReset 1 = 0 := by
  refine ⟨resetThenFlip_weight, ?_⟩
  norm_num [futureStateWeights, Matrix.vecMul_apply_eq_sum, transitionMatrix, resetFlip, ν,
    flipThenReset, Fin.sum_univ_two, StdSimplex.weights_single, Finsupp.single_apply]

-- At positive time, a reachable state outside reference support makes the maximum infinite.
example : futureDistributionCoefficient resetFlip ν ν 2 = ∞ := by
  have h := futureWeightRatio_le_coefficient resetFlip ν ν 1 resetThenFlip 1
  have hzero : ν.weights (1 : Fin 2) = 0 := by
    norm_num [ν, StdSimplex.weights_single, Finsupp.single_apply]
  rw [resetThenFlip_weight, hzero, futureWeightRatio_zero_right_of_pos (by norm_num)] at h
  exact top_unique h

-- Time zero does not use the mass-ratio formula, even for disjoint initial and reference laws.
example : futureDistributionCoefficient resetFlip ν (StdSimplex.single 1) 0 = 1 :=
  futureDistributionCoefficient_zero _ _ _

example : futureWeightRatio 0 0 = 0 := futureWeightRatio_zero_left _

example : futureWeightRatio (1 / 2) (1 / 4) = 2 := by
  rw [futureWeightRatio_of_pos (by norm_num)]
  norm_num

private noncomputable def uniformTwo : StdSimplex ℝ (Fin 2) where
  weights := Finsupp.equivFunOnFinite.symm (fun _ => 1 / 2)
  nonneg := fun i => by change (0 : ℝ) ≤ 1 / 2; norm_num
  total := by
    rw [Finsupp.sum_fintype _ _ (by simp)]
    change (∑ _i : Fin 2, (1 / 2 : ℝ)) = 1
    norm_num [Fin.sum_univ_two]

private theorem resetFlip_stochastic : resetFlip.Stochastic := by
  refine ⟨?_, ?_⟩
  · intro x a y
    simp only [resetFlip]
    split_ifs <;> norm_num
  · intro x a
    simp only [resetFlip]
    simp

-- With full reference support, the maximum is finite and is attained by a deterministic
-- trajectory with mass one at a destination of reference mass one half.
example : futureDistributionCoefficient resetFlip ν uniformTwo 2 = 2 := by
  apply le_antisymm
  · change (⨆ z : (Fin 2 → Fin 2 → Bool) × Fin 2,
      futureWeightRatio (futureStateWeights resetFlip ν 2 z.1 z.2) (uniformTwo.weights z.2)) ≤ 2
    apply iSup_le
    intro z
    obtain ⟨hn, hs⟩ := futureStateWeights_stochastic resetFlip_stochastic ν 2 z.1
    have hle : futureStateWeights resetFlip ν 2 z.1 z.2 ≤ 1 := by
      rw [← hs]
      exact Finset.single_le_sum (fun i _ => hn i) (Finset.mem_univ z.2)
    change futureWeightRatio (futureStateWeights resetFlip ν 2 z.1 z.2) (1 / 2) ≤ 2
    rw [futureWeightRatio_of_pos (by norm_num)]
    calc _ ≤ ENNReal.ofReal (1 / (1 / 2 : ℝ)) :=
          ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hle (by norm_num))
      _ = 2 := by norm_num
  · have h := futureWeightRatio_le_coefficient resetFlip ν uniformTwo 1 resetThenFlip 1
    change futureWeightRatio (futureStateWeights resetFlip ν 2 resetThenFlip 1) (1 / 2) ≤ _ at h
    rw [resetThenFlip_weight, futureWeightRatio_of_pos (by norm_num)] at h
    norm_num at h
    exact h

end CSLibExtTest.Algorithms.Lean.MDP.FutureDistribution
