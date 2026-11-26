/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.ClusterMoments

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.ClusterMoments`

* `clusterMoment_le_of_geometricTail` and `clusterSizeDomination_of_geometricTail` for the
  geometric tail `dist n = (1/2) ^ n`;
* `ClusterSizeDomination.allMoments_lt_top` for that domination;
* `subcritical_expectedProgeny` at `b = 1`, `p = 1/2`: the expected progeny is `2`;
* `subcritical_expMomentRadius` at `b = 2`, `p = 1/4`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.CriticalPoint.ClusterMoments

open _root_.StatMech _root_.StatMech.BeffaraDC

/-- The geometric tail `(1/2) ^ n`. -/
noncomputable def geomDist (n : ℕ) : ℝ := (1 / 2) ^ n

-- The first moment of the geometric tail is bounded by the geometric series.
example : clusterMoment geomDist 1 ≤ ∑' n : ℕ, (n : ℝ) ^ 1 * (1 * (1 / 2) ^ n) :=
  clusterMoment_le_of_geometricTail (by norm_num) (by norm_num)
    (fun n => by unfold geomDist; positivity) (fun n => by simp [geomDist]) 1

/-- The geometric tail as a cluster-size domination. -/
noncomputable def geomDom : ClusterSizeDomination :=
  clusterSizeDomination_of_geometricTail (dist := geomDist) (C := 1) (r := 1 / 2)
    (fun n => by unfold geomDist; positivity) (by norm_num) (by norm_num)
    (fun n => by simp [geomDist])

-- All moments of the packaged domination are finite.
example (d : ℕ) := geomDom.allMoments_lt_top d

-- A binary-free branching process with `p = 1/2` has expected progeny `2`.
example : ∑' k : ℕ, (((1 : ℕ) : ℝ) * (1 / 2)) ^ k = 2 := by
  rw [subcritical_expectedProgeny 1 (by norm_num) (by norm_num)]
  norm_num

-- The subcritical binary tree at `p = 1/4` has generating-function radius above `1`.
example : ∃ s, 1 < s ∧ Percolation.treeGF 2 (1 / 4) s < s :=
  subcritical_expMomentRadius 2 (by norm_num)

end PhyslibExtTest.StatisticalMechanics.RandomCluster.CriticalPoint.ClusterMoments
