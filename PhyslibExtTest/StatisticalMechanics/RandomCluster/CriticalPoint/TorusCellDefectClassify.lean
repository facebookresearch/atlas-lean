/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.TorusCellDefectClassify

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.TorusCellDefectClassify`

On the `3 × 3` torus:
* `torusCellDefect_classified_unconditional` for the empty and the full subgraph;
* `torusCellCutDualGraph_degree_even` for the cut of `{(0, 0)}`;
* `torusCellDefect_le_sup_edge`: adding the edge `(0, 0)–(1, 0)` to the empty subgraph does not
  lower the defect.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.CriticalPoint.TorusCellDefectClassify

open _root_.StatMech _root_.StatMech.BeffaraDC _root_.StatMech.Onsager

instance : Fact (2 < 3) := ⟨by norm_num⟩

-- The defect of the empty subgraph is `0`, `1` or `2`.
example := torusCellDefect_classified_unconditional 3 ⊥ bot_le

-- The defect of the full torus is `0`, `1` or `2`.
example := torusCellDefect_classified_unconditional 3 (onsTorusGraph 3) le_rfl

-- Cut dual graphs have even degrees.
example (v : ZMod 3 × ZMod 3) := torusCellCutDualGraph_degree_even 3 {(0, 0)} v

-- Adding one torus edge does not lower the defect.
example : torusCellDefect 3 ⊥ ≤ torusCellDefect 3 (⊥ ⊔ SimpleGraph.edge (0, 0) (1, 0)) :=
  torusCellDefect_le_sup_edge 3 ⊥ (by decide) (fun h => h)

end PhyslibExtTest.StatisticalMechanics.RandomCluster.CriticalPoint.TorusCellDefectClassify
