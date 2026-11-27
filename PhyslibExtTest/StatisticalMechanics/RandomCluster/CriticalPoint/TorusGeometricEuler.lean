/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.TorusGeometricEuler

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.TorusGeometricEuler`

On the `3 × 3` torus:
* `torusQuarterTurn_apply` at `(1, 2)`;
* `torusGeometricFaceCount_full`: the full torus has `9` geometric faces;
* `torusDualCutGraph_bot` and `geometric_euler_torus` for the empty subgraph;
* `torusGeometricDefect_full` and `torusGeometricDefect_bot` in conditional form (connectivity of
  the torus is proved in `TorusConnected`, which this module does not import).
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.CriticalPoint.TorusGeometricEuler

open _root_.StatMech _root_.StatMech.BeffaraDC _root_.StatMech.Onsager

instance : Fact (2 < 3) := ⟨by norm_num⟩

-- The quarter turn sends `(1, 2)` to `(2, 2)` on `ZMod 3 × ZMod 3`.
example : torusQuarterTurn 3 (1, 2) = (2, 2) := by
  rw [torusQuarterTurn_apply]
  decide

-- The full `3 × 3` torus has `9` geometric faces.
example : torusGeometricFaceCount 3 (onsTorusGraph 3) = 9 := torusGeometricFaceCount_full 3

-- The dual cut graph of the empty subgraph is the whole torus.
example : torusDualCutGraph 3 ⊥ = onsTorusGraph 3 := torusDualCutGraph_bot 3

-- The geometric Euler relation for the empty subgraph.
example := geometric_euler_torus 3 ⊥

-- Defects of the empty and the full subgraph, given connectivity.
example (hconn : (onsTorusGraph 3).Connected) :
    torusGeometricDefect 3 ⊥ = 0 ∧ torusGeometricDefect 3 (onsTorusGraph 3) = 2 :=
  ⟨torusGeometricDefect_bot 3 hconn, torusGeometricDefect_full 3 hconn⟩

end PhyslibExtTest.StatisticalMechanics.RandomCluster.CriticalPoint.TorusGeometricEuler
