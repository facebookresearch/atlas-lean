/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.ClusterSizeMoments

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.ClusterSizeMoments`

On the empty graph on `Fin 2` at `p = 1/2`:
* `fkClusterSizeTail_eq_zero_of_card_lt` for clusters of size `3`;
* `fkClusterSizeTail_le_bernoulli` at `q = 2`;
* `exists_geometricTail` feeding `fkClusterSizeMoment_lt_top`: the second moment of the cluster
  size at `q = 2` is bounded by a geometric series (the conditional hypothesis is discharged);
* `fkClusterSizeLargeEvent_isIncreasing`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.CriticalPoint.ClusterSizeMoments

open _root_.StatMech _root_.StatMech.BeffaraDC _root_.StatMech.FK

-- No cluster of the two-vertex graph has `3` vertices.
example : fkClusterSizeTail (⊥ : SimpleGraph (Fin 2)) (1 / 2) 2 0 3 = 0 :=
  fkClusterSizeTail_eq_zero_of_card_lt _ _ _ _ (by simp)

-- Domination of the `q = 2` tail by the Bernoulli tail.
example (N : ℕ) : fkClusterSizeTail (⊥ : SimpleGraph (Fin 2)) (1 / 2) 2 0 N
    ≤ fkClusterSizeTail (⊥ : SimpleGraph (Fin 2)) (1 / 2) 1 0 N :=
  fkClusterSizeTail_le_bernoulli _ (by norm_num) (by norm_num) (by norm_num) 0 N

-- The geometric-tail hypothesis is satisfiable, so the moment bound applies.
example : ∃ C r : ℝ, clusterMoment
    (fun N => fkClusterSizeTail (⊥ : SimpleGraph (Fin 2)) (1 / 2) 2 0 N) 2
      ≤ ∑' N : ℕ, (N : ℝ) ^ 2 * (C * r ^ N) := by
  obtain ⟨C, r, hr0, hr1, h⟩ :=
    exists_geometricTail (⊥ : SimpleGraph (Fin 2)) (p := 1 / 2) (q := 1)
      (by norm_num) (by norm_num) one_pos 0
  exact ⟨C, r, fkClusterSizeMoment_lt_top _ (by norm_num) (by norm_num) (by norm_num) 0
    hr0 hr1 h 2⟩

-- Large-cluster events are increasing.
example := fkClusterSizeLargeEvent_isIncreasing (⊥ : SimpleGraph (Fin 2)) 0 2

end PhyslibExtTest.StatisticalMechanics.RandomCluster.CriticalPoint.ClusterSizeMoments
