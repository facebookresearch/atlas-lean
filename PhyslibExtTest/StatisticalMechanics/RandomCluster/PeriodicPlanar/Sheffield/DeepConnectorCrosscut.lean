/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.DeepConnectorCrosscut

/-!
# Tests for `Sheffield.DeepConnectorCrosscut`

Module under test: `Sheffield.DeepConnectorCrosscut` in
`PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar`.

* `PeriodicPlaneEmbedding.finiteDeepOpenExitedJoinedBoundaryArmEvent_openWalk` applied with
  `r = R` (the boundary case of `r ≤ R`).
* `PeriodicPlaneEmbedding.finiteDeepOpenExitedJoinedBoundaryArmEvent_simpleCrosscut` applied with
  `r = 0 ≤ 1 = R` and `c = 0 < 1 = d`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield
namespace DeepConnectorCrosscut

open _root_.StatMech _root_.StatMech.FK.PeriodicPlanar

variable {V : Type*} [DecidableEq V] [Countable V] {P : PeriodicGraph V}

-- An open walk through both boundary rays, with `r = R`.
example (E : PeriodicPlaneEmbedding P) (omega : ConfigSpace (Sym2 V)) (r c d : ℝ) (w : ℕ)
    (L U : Finset V) (h : omega ∈ E.finiteDeepOpenExitedJoinedBoundaryArmEvent r r c d w L U) :=
  E.finiteDeepOpenExitedJoinedBoundaryArmEvent_openWalk le_rfl h

-- A simple open crosscut, with explicit `r ≤ R` and `c < d`.
example (E : PeriodicPlaneEmbedding P) (omega : ConfigSpace (Sym2 V)) (w : ℕ) (L U : Finset V)
    (h : omega ∈ E.finiteDeepOpenExitedJoinedBoundaryArmEvent 0 1 0 1 w L U) :=
  E.finiteDeepOpenExitedJoinedBoundaryArmEvent_simpleCrosscut zero_le_one zero_lt_one h

end DeepConnectorCrosscut
end PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield
