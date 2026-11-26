/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.TorusCellDual

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.TorusCellDual`

On the `3 × 3` torus:
* `torusCell_euler` for the empty subgraph;
* `torusCell_numClusters_dualConfig` for the all-closed configuration;
* `torusCellDualCutGraph_bot` and `torusCellFaceCount_full` (`9` faces);
* `torusCellDefect_bot` and `torusCellDefect_full` in conditional form (connectivity is proved in
  `TorusConnected`, which this module does not import).
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.CriticalPoint.TorusCellDual

open _root_.StatMech _root_.StatMech.BeffaraDC _root_.StatMech.Onsager

instance : Fact (2 < 3) := ⟨by norm_num⟩

-- Euler's relation with defect for the empty subgraph.
example := torusCell_euler 3 ⊥

-- Clusters of the dual configuration are faces.
example := torusCell_numClusters_dualConfig 3 (fun _ => false)

-- The dual cut graph of the empty subgraph is the whole torus.
example : torusCellDualCutGraph 3 ⊥ = onsTorusGraph 3 := torusCellDualCutGraph_bot 3

-- The full `3 × 3` torus has `9` cell faces.
example : torusCellFaceCount 3 (onsTorusGraph 3) = 9 := torusCellFaceCount_full 3

-- Defects of the empty and full subgraph, given connectivity.
example (hconn : (onsTorusGraph 3).Connected) :
    torusCellDefect 3 ⊥ = 0 ∧ torusCellDefect 3 (onsTorusGraph 3) = 2 :=
  ⟨torusCellDefect_bot 3 hconn, torusCellDefect_full 3 hconn⟩

end PhyslibExtTest.StatisticalMechanics.RandomCluster.CriticalPoint.TorusCellDual
