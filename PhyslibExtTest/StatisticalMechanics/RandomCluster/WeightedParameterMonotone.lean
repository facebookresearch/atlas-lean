/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.WeightedParameterMonotone

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.WeightedParameterMonotone`

On the one-edge graph `⊤` on `Fin 2` with empty wiring, `q = 2`, comparing the boundary parameter
`p ≡ 0` with `p ≡ 1/2`:
* `bcProbW_sum_eq_one_of_nonneg` at `p ≡ 0` (zero parameters are allowed);
* `bcWeightW_cross_params_of_nonneg` at the all-closed and all-open configurations;
* `bcProbW_mono_params_of_nonneg` for the event "the edge `s(0, 1)` is open".
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.WeightedParameterMonotone

open _root_.StatMech _root_.StatMech.FK

/-- The one-edge test graph. -/
abbrev G2 : SimpleGraph (Fin 2) := ⊤

-- With all parameters zero the measure is still a probability mass function.
example : (∑ ω, bcProbW G2 ⊥ (fun _ => 0) 2 ω) = 1 :=
  bcProbW_sum_eq_one_of_nonneg G2 ⊥ (fun _ => le_rfl) (fun _ => one_pos) two_pos

-- Holley's cross condition for `0 ≤ 1/2`.
example : bcWeightW G2 ⊥ (fun _ => 0) 2 (fun _ => false) *
      bcWeightW G2 ⊥ (fun _ => 1 / 2) 2 (fun _ => true) ≤
    bcWeightW G2 ⊥ (fun _ => 0) 2 ((fun _ => false) ⊓ fun _ => true) *
      bcWeightW G2 ⊥ (fun _ => 1 / 2) 2 ((fun _ => false) ⊔ fun _ => true) :=
  bcWeightW_cross_params_of_nonneg G2 ⊥ (fun _ => le_rfl) (fun _ => one_pos)
    (fun _ => by norm_num) (fun _ => by norm_num) (fun _ => by norm_num) one_le_two _ _

/-- "The edge `s(0, 1)` is open" is increasing. -/
theorem edgeOpen_isIncreasing :
    IsIncreasing {ω : ConfigSpace (Sym2 (Fin 2)) | ω s(0, 1) = true} := by
  intro x y hxy hx
  have h := hxy s(0, 1)
  simp only [Set.mem_ofPred_eq] at hx ⊢
  rw [hx] at h
  exact top_le_iff.mp h

-- Larger parameters make the open edge more likely.
example := bcProbW_mono_params_of_nonneg G2 ⊥ (pf1 := fun _ => 0) (pf2 := fun _ => 1 / 2)
  (fun _ => le_rfl) (fun _ => one_pos) (fun _ => by norm_num) (fun _ => by norm_num)
  (fun _ => by norm_num) one_le_two edgeOpen_isIncreasing

end PhyslibExtTest.StatisticalMechanics.RandomCluster.WeightedParameterMonotone
