/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.TorusCellFKDuality

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.TorusCellFKDuality`

On the `3 × 3` torus:
* `torusCell_clusterEuler_signed` for the empty subgraph;
* `torusCell_primalWeight_openSub` for the all-closed configuration;
* `torusCell_weight_duality_signed` for the empty subgraph at `p = 1/2`, `q = 2`;
* `torusCell_fkWeight_duality_signed` for the all-closed configuration at `p = 1/2`, `q = 2`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.CriticalPoint.TorusCellFKDuality

open _root_.StatMech _root_.StatMech.BeffaraDC _root_.StatMech.Onsager

instance : Fact (2 < 3) := ⟨by norm_num⟩

-- The signed Euler relation for the empty subgraph of the `3 × 3` torus.
example := torusCell_clusterEuler_signed 3 ⊥

-- The primal weight of the open subgraph of the all-closed configuration.
example (p q : ℝ) := torusCell_primalWeight_openSub 3 p q (fun _ => false)

-- Weight duality for the empty subgraph at `p = 1/2`, `q = 2`.
example := torusCell_weight_duality_signed 3 ⊥ bot_le (p := 1 / 2) (q := 2)
  (by norm_num) (by norm_num) (by norm_num)

-- Random-cluster weight duality for the all-closed configuration at `p = 1/2`, `q = 2`.
example := torusCell_fkWeight_duality_signed 3 (fun _ => false) (p := 1 / 2) (q := 2)
  (by norm_num) (by norm_num) (by norm_num)

end PhyslibExtTest.StatisticalMechanics.RandomCluster.CriticalPoint.TorusCellFKDuality
