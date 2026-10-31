/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.MaxInfluenceHalf

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.MaxInfluenceHalf`

On `ConfigSpace (Fin 2)` with the increasing event `A = {ω | ω 0 = true}`, of probability `1/2`:
* `maxInfluence_half` and `maxInfluence_half_of_increasing` (KKL lower bound);
* `exists_influence_pos_half_of_nontrivial`, with its nontriviality hypotheses discharged
  (`P(A) = 1/2`), so some coordinate has positive influence.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.CriticalPoint.MaxInfluenceHalf

open _root_.StatMech _root_.StatMech.BeffaraDC

/-- The event "coordinate `0` is open". -/
def A : Set (ConfigSpace (Fin 2)) := {ω | ω 0 = true}

/-- `A` is increasing. -/
theorem A_isIncreasing : IsIncreasing A := by
  intro x y hxy hx
  have h := hxy 0
  simp only [A, Set.mem_ofPred_eq] at hx ⊢
  rw [hx] at h
  exact top_le_iff.mp h

/-- `A` has probability `1/2` at `p = 1/2`. -/
theorem prob_A : StatMech.prob (1 / 2 : ℝ) A = 1 / 2 := by
  rw [StatMech.prob, ← Equiv.sum_comp (piFinTwoEquiv (fun _ : Fin 2 => Bool)).symm]
  norm_num [A, Fintype.sum_prod_type, configWeight, edgeWeight, Fin.prod_univ_two, Set.indicator]

-- KKL at `p = 1/2` for `A`.
example : ∃ e : Fin 2, StatMech.prob (1 / 2 : ℝ) A * (1 - StatMech.prob (1 / 2 : ℝ) A)
    * Real.log (Fintype.card (Fin 2) : ℝ) / (Fintype.card (Fin 2) : ℝ)
      ≤ influence (1 / 2 : ℝ) A e :=
  maxInfluence_half A

-- The increasing-event form.
example := maxInfluence_half_of_increasing A A_isIncreasing

-- A nontrivial event has a coordinate of positive influence.
example : ∃ e : Fin 2, 0 < influence (1 / 2 : ℝ) A e :=
  exists_influence_pos_half_of_nontrivial A (by simp) (by rw [prob_A]; norm_num)
    (by rw [prob_A]; norm_num)

end PhyslibExtTest.StatisticalMechanics.RandomCluster.CriticalPoint.MaxInfluenceHalf
