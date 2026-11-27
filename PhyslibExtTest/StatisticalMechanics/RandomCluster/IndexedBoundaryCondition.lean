/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.IndexedBoundaryCondition

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.IndexedBoundaryCondition`

On the multigraph with two parallel edges `Fin 2 → Sym2 (Fin 2)`, both joining `0` and `1`, with
boundary wirings `⊥ ≤ ⊤`, at `p = 1/2`, `q = 2`:
* `indexedBcProb_sum_eq_one`: the indexed measure is a probability mass function;
* `indexedMixed_supermodular_bc` at the all-closed and all-open configurations;
* `indexedBcEventMass_mono_bc` for the increasing event "edge `0` is open".
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.IndexedBoundaryCondition

open _root_.StatMech _root_.StatMech.FK

/-- Two parallel edges between `0` and `1`. -/
def ends2 : Fin 2 → Sym2 (Fin 2) := fun _ => s(0, 1)

-- The indexed measure sums to one.
example : ∑ ω : Fin 2 → Bool, indexedBcProb ends2 ⊥ (1 / 2) 2 ω = 1 :=
  indexedBcProb_sum_eq_one _ _ (by norm_num) (by norm_num) (by norm_num)

-- Mixed supermodularity of the cluster count for `⊥ ≤ ⊤`.
example : indexedNumClustersBC ends2 ⊥ (fun _ => false) +
      indexedNumClustersBC ends2 ⊤ (fun _ => true) ≤
    indexedNumClustersBC ends2 ⊥ ((fun _ => false) ⊓ fun _ => true) +
      indexedNumClustersBC ends2 ⊤ ((fun _ => false) ⊔ fun _ => true) :=
  indexedMixed_supermodular_bc _ ⊥ ⊤ bot_le _ _

/-- "Edge `0` is open" is increasing. -/
theorem edge0_isIncreasing : IsIncreasing {ω : ConfigSpace (Fin 2) | ω 0 = true} := by
  intro x y hxy hx
  have h := hxy 0
  simp only [Set.mem_ofPred_eq] at hx ⊢
  rw [hx] at h
  exact top_le_iff.mp h

-- A larger wiring makes increasing events more likely.
example : indexedBcEventMass ends2 ⊥ (1 / 2) 2 {ω | ω 0 = true} ≤
    indexedBcEventMass ends2 ⊤ (1 / 2) 2 {ω | ω 0 = true} :=
  indexedBcEventMass_mono_bc _ ⊥ ⊤ bot_le (by norm_num) (by norm_num) one_le_two
    edge0_isIncreasing

end PhyslibExtTest.StatisticalMechanics.RandomCluster.IndexedBoundaryCondition
