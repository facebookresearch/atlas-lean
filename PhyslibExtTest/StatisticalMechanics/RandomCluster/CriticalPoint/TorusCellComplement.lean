/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.TorusCellComplement

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.TorusCellComplement`

On the `3 × 3` torus:
* `torusCellDiagonalShift_apply` at `(1, 2)`;
* `torusCellDefect_add_dualConfig` for the all-closed configuration (defects sum to `2`);
* `torusCell_numClusters_dualConfig_dualConfig` and `torusCell_openSub_dualConfig_dualConfig`
  for the all-open configuration;
* `torusCellDefect_add_dualCutGraph` for the empty subgraph.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.CriticalPoint.TorusCellComplement

open _root_.StatMech _root_.StatMech.BeffaraDC _root_.StatMech.Onsager

instance : Fact (2 < 3) := ⟨by norm_num⟩

-- The diagonal shift sends `(1, 2)` to `(2, 0)` on `ZMod 3 × ZMod 3`.
example : torusCellDiagonalShift 3 (1, 2) = (2, 0) := by
  rw [torusCellDiagonalShift_apply]
  decide

-- A configuration and its cell dual have defects summing to `2`.
example := torusCellDefect_add_dualConfig 3 (fun _ => false)

-- Double duality preserves the cluster count.
example := torusCell_numClusters_dualConfig_dualConfig 3 (fun _ => true)

-- Double duality is the diagonal shift on open subgraphs.
example := torusCell_openSub_dualConfig_dualConfig 3 (fun _ => true)

-- The empty subgraph and its dual cut graph.
example := torusCellDefect_add_dualCutGraph 3 ⊥ bot_le

end PhyslibExtTest.StatisticalMechanics.RandomCluster.CriticalPoint.TorusCellComplement
