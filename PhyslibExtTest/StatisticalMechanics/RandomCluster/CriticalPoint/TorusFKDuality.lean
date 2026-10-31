/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.TorusFKDuality

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.TorusFKDuality`

On the `3 × 3` torus:
* `torus_weight_duality_signed` for the empty subgraph at `p = 1/2`, `q = 2` (unconditional);
* `torus_numClusters_dualConfig` for the all-closed configuration;
* `torus_normalized_event_comparison` in conditional form, given `TorusDefectClassified 3`;
* `TorusDefectClassified` has content: its defining disjunction holds at the empty subgraph
  given connectivity (defect `0`).
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.CriticalPoint.TorusFKDuality

open _root_.StatMech _root_.StatMech.BeffaraDC _root_.StatMech.Onsager

instance : Fact (2 < 3) := ⟨by norm_num⟩

-- Signed weight duality for the empty subgraph.
example := torus_weight_duality_signed 3 ⊥ bot_le (p := 1 / 2) (q := 2)
  (by norm_num) (by norm_num) (by norm_num)

-- Clusters of the quarter-turn dual configuration.
example := torus_numClusters_dualConfig 3 (fun _ => false)

-- The normalized event comparison, given the defect classification.
example (hclass : TorusDefectClassified 3)
    (A : Finset (ConfigSpace (Sym2 (ZMod 3 × ZMod 3)))) :=
  torus_normalized_event_comparison 3 hclass (p := 1 / 2) (q := 2) (by norm_num) (by norm_num)
    (by norm_num) A

-- The classification disjunction holds for the empty subgraph, given connectivity.
example (hconn : (onsTorusGraph 3).Connected) :
    torusGeometricDefect 3 ⊥ = 0 ∨ torusGeometricDefect 3 ⊥ = 1 ∨
      torusGeometricDefect 3 ⊥ = 2 :=
  Or.inl (torusGeometricDefect_bot 3 hconn)

end PhyslibExtTest.StatisticalMechanics.RandomCluster.CriticalPoint.TorusFKDuality
