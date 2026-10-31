/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.Hamming

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.Hamming`

On `ConfigSpace (Fin 2)` with the increasing event `A = {ω | ω 0 = true}`:
* `hammingToSet A` of the all-closed configuration is `1` (upper bound from `hammingToSet_le`,
  lower bound from `hammingToSet_eq_zero_iff`);
* `hammingToSet_eq_zero_of_mem` on the all-open configuration;
* `hammingToSet_antitone` comparing all-closed with all-open.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.CriticalPoint.Hamming

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

/-- The all-closed configuration is at Hamming distance `1` from `A`. -/
theorem hammingToSet_A_false : hammingToSet A (fun _ => false) = 1 := by
  have hle : hammingToSet A (fun _ => false) ≤ 1 :=
    (hammingToSet_le A (a := ![true, false]) rfl _).trans (by decide)
  have hne : hammingToSet A (fun _ => false) ≠ 0 := by
    rw [Ne, hammingToSet_eq_zero_iff A ⟨fun _ => true, rfl⟩]
    simp [A]
  omega

-- A configuration in `A` is at distance `0`.
example : hammingToSet A (fun _ => true) = 0 := hammingToSet_eq_zero_of_mem A rfl

-- Antitonicity: the larger configuration is closer to the increasing event.
example : hammingToSet A (fun _ => true) ≤ hammingToSet A (fun _ => false) :=
  hammingToSet_antitone A A_isIncreasing (fun _ => le_top)

end PhyslibExtTest.StatisticalMechanics.RandomCluster.CriticalPoint.Hamming
