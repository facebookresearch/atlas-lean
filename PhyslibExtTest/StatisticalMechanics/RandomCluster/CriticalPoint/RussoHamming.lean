/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.RussoHamming

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.RussoHamming`

On `ConfigSpace (Fin 2)` with the increasing event `A = {ω | ω 0 = true}`:
* `numOpen` of the all-open configuration is `2`;
* `russoHamming` at `p = 1/2`;
* `russoHammingIntegrated` at `p₁ = 1/3`, `p₂ = 2/3`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.CriticalPoint.RussoHamming

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

-- Both edges of the all-open configuration are open.
example : numOpen (fun _ : Fin 2 => true) = 2 := by decide

-- The Russo–Hamming derivative bound at `p = 1/2`.
example := russoHamming (p := 1 / 2) (by norm_num) (by norm_num) A A_isIncreasing

-- The integrated comparison between `1/3` and `2/3`.
example := russoHammingIntegrated (p₁ := 1 / 3) (p₂ := 2 / 3) (by norm_num) (by norm_num)
  (by norm_num) A A_isIncreasing

end PhyslibExtTest.StatisticalMechanics.RandomCluster.CriticalPoint.RussoHamming
