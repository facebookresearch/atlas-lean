/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.TorusDefectComplement

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.TorusDefectComplement`

On the `3 × 3` torus:
* `torusHalfTurn_apply` at the vertex `(1, 2)`, and `torusHalfTurn_adj_iff`;
* `torusGeometricDefect_add_dual` for the all-closed configuration (defects sum to `2`);
* `torus_openSub_configOfGraph` and `torusGeometricDefect_add_dualCutGraph` for the empty subgraph.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.CriticalPoint.TorusDefectComplement

open _root_.StatMech _root_.StatMech.BeffaraDC _root_.StatMech.Onsager

instance : Fact (2 < 3) := ⟨by norm_num⟩

-- The half turn sends `(1, 2)` to `(2, 1)` on `ZMod 3 × ZMod 3`.
example : torusHalfTurn 3 (1, 2) = (2, 1) := by
  rw [torusHalfTurn_apply]
  decide

-- The half turn preserves adjacency.
example (u v : ZMod 3 × ZMod 3) :
    (onsTorusGraph 3).Adj (torusHalfTurn 3 u) (torusHalfTurn 3 v) ↔ (onsTorusGraph 3).Adj u v :=
  torusHalfTurn_adj_iff 3 u v

-- The all-closed configuration and its dual have defects summing to `2`.
example := torusGeometricDefect_add_dual 3 (fun _ => false)

-- The configuration of the empty subgraph recovers it.
example := torus_openSub_configOfGraph 3 ⊥ bot_le

-- The empty subgraph and its dual cut graph have defects summing to `2`.
example := torusGeometricDefect_add_dualCutGraph 3 ⊥ bot_le

end PhyslibExtTest.StatisticalMechanics.RandomCluster.CriticalPoint.TorusDefectComplement
