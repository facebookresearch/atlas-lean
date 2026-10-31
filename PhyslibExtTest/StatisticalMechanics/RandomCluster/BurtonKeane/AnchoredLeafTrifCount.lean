/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.AnchoredLeafTrifCount

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.AnchoredLeafTrifCount`

* `bc121_leaf_has_neighbour` on the complete graph on `Fin 2` (every vertex is a leaf);
* `bc121_boundaryAnchored_subforest` applied to the empty graph on `Fin 3`;
* `bc121_deg3_of_three_reached_targets` and `bc121_count_via_peel2` checked by type.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.AnchoredLeafTrifCount

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.ConfigSpace
open _root_.StatMech.Percolation _root_.StatMech.Walls

/-- Both vertices of the complete graph on `Fin 2` are leaves. -/
theorem top_fin2_degree (v : Fin 2) : (⊤ : SimpleGraph (Fin 2)).degree v = 1 := by
  simp

-- A leaf has a neighbour.
example : ∃ w, (⊤ : SimpleGraph (Fin 2)).Adj 0 w :=
  bc121_leaf_has_neighbour ⊤ (top_fin2_degree 0)

-- An acyclic graph has a boundary-anchored subforest (concrete instance).
example := bc121_boundaryAnchored_subforest (⊥ : SimpleGraph (Fin 3)) (fun v => v = 0)
  SimpleGraph.isAcyclic_bot

-- The degree-three criterion and the peeled count, by type.
example := @bc121_deg3_of_three_reached_targets
example := @bc121_count_via_peel2

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.AnchoredLeafTrifCount
