/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Algorithms.Lean.MDP.TransitionConcentration
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! # Regressions for transition concentration -/

open Convexity Cslib.Algorithms.Lean.MarkovDecision
open scoped ENNReal

namespace CSLibExtTest.Algorithms.Lean.MDP.TransitionConcentration

private noncomputable def reference : StdSimplex ℝ (Fin 2) := StdSimplex.single 0

-- Every move lands at zero. Zero reference mass at state one is harmless: its
-- transition weights are also zero, so those ratios do not raise the maximum.
private def reset : MDP (Fin 2) Unit ℝ where
  reward := fun _ _ => 0
  prob := fun _ _ y => if y = 0 then 1 else 0

example : transitionConcentrationCoefficient reset reference = 1 := by
  apply le_antisymm
  · rw [transitionConcentrationCoefficient_le_iff]
    intro s a y
    fin_cases y <;> norm_num [reset, reference, StdSimplex.weights_single, Finsupp.single_apply]
  · have h := (transitionConcentrationCoefficient_le_iff reset reference
      (transitionConcentrationCoefficient reset reference)).mp le_rfl 1 () 0
    simpa [reset, reference, StdSimplex.weights_single, Finsupp.single_apply] using h

-- The extra action stays at the source. The transition from state one to itself
-- witnesses infinity, although the reset action alone has a finite coefficient.
private def resetOrStay : MDP (Fin 2) Bool ℝ where
  reward := fun _ _ => 0
  prob := fun s a y => if y = (if a then s else 0) then 1 else 0

example : transitionConcentrationCoefficient resetOrStay reference = ∞ := by
  apply (transitionConcentrationCoefficient_eq_top_iff _ _).mpr
  refine ⟨1, true, 1, ?_, ?_⟩
  · norm_num [resetOrStay]
  · norm_num [reference, StdSimplex.weights_single, Finsupp.single_apply]

private noncomputable def uniformTwo : StdSimplex ℝ (Fin 2) where
  weights := Finsupp.equivFunOnFinite.symm (fun _ => 1 / 2)
  nonneg := fun _ => by change (0 : ℝ) ≤ 1 / 2; norm_num
  total := by
    rw [Finsupp.sum_fintype _ _ (by simp)]
    change (∑ _i : Fin 2, (1 / 2 : ℝ)) = 1
    norm_num [Fin.sum_univ_two]

-- A full-support reference gives a finite maximum, and the ratio can exceed one.
example : transitionConcentrationCoefficient reset uniformTwo = 2 := by
  have hbound := transitionConcentrationCoefficient_le_iff reset uniformTwo
  have hμ : ∀ y, uniformTwo.weights y = 1 / 2 := fun _ => rfl
  apply le_antisymm
  · apply (hbound 2).mpr
    intro s a y
    rw [hμ, ← ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    by_cases hy : y = 0 <;> norm_num [reset, hy]
  · have h := (hbound _).mp le_rfl 1 () 0
    rw [hμ, ← ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at h
    norm_num [reset] at h
    exact h

end CSLibExtTest.Algorithms.Lean.MDP.TransitionConcentration
