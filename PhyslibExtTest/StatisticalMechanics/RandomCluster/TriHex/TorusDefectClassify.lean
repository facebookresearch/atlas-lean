/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.TriHex.TorusDefectClassify

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.TriHex.TorusDefectClassify`

On the torus of side `3`:
* the empty subgraph has defect `0` and the full triangular torus has defect `2`, so both extreme
  values of `triHexTorusDefect_classified` occur;
* `triHexTorusDefect_classified` applied to the empty subgraph;
* `triangularTorusGraph_connected` and `hexagonalTorusGraph_connected`;
* `triHexTorusDualCutGraph_bot`: the dual cut graph of the empty subgraph is the hexagonal torus.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.TriHex.TorusDefectClassify

open _root_.StatMech.FK.PeriodicPlanar

instance : Fact (2 < 3) := ⟨by norm_num⟩

-- The extreme defects.
example : triHexTorusEulerDefect 3 ⊥ = 0 ∧
    triHexTorusEulerDefect 3 (triangularTorusGraph 3) = 2 :=
  ⟨triHexTorusDefect_bot 3, triHexTorusDefect_full 3⟩

-- The classification applied to the empty subgraph.
example : triHexTorusEulerDefect 3 ⊥ = 0 ∨ triHexTorusEulerDefect 3 ⊥ = 1 ∨
    triHexTorusEulerDefect 3 ⊥ = 2 :=
  triHexTorusDefect_classified 3 ⊥ bot_le

-- Both tori are connected.
example : (triangularTorusGraph 3).Connected ∧ (hexagonalTorusGraph 3).Connected :=
  ⟨triangularTorusGraph_connected 3, hexagonalTorusGraph_connected 3⟩

-- Removing no primal edges leaves the whole hexagonal torus as the dual cut graph.
example : triHexTorusDualCutGraph 3 ⊥ = hexagonalTorusGraph 3 :=
  triHexTorusDualCutGraph_bot 3

end PhyslibExtTest.StatisticalMechanics.RandomCluster.TriHex.TorusDefectClassify
