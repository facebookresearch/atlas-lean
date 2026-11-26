/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.TreeCutVertex

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.TreeCutVertex`

* instance: the explicit spanning tree `bcv_T0` of the graph `bgn_W` (`bcv_T0_witness`): connected,
  with degrees `5` and `3` at the two hubs;
* `bcv_bgnW_connected` and `bcv_bgnW_spanningTree_deg3`;
* `bcv_sep3` on the edgeless graph on `Fin 3`;
* `bcv_count_of_treeData` in conditional form.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.TreeCutVertex

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.Percolation _root_.StatMech.Walls
open _root_.StatMech.ConfigSpace MeasureTheory

-- The explicit spanning tree and its hub degrees.
example : bcv_T0 ≤ bgn_W ∧ bcv_T0.Connected ∧ bcv_T0.degree 0 = 5 ∧ bcv_T0.degree 1 = 3 :=
  ⟨bcv_T0_witness.1, bcv_T0_witness.2.1, bcv_T0_witness.2.2.1, bcv_T0_witness.2.2.2.1⟩

-- `bgn_W` is connected and has a spanning tree with two hubs of degree at least three.
example : bgn_W.Connected ∧ ∃ T : SimpleGraph (Fin 8), T ≤ bgn_W ∧ T.IsTree ∧
    (∀ (_ : DecidableRel T.Adj), 3 ≤ T.degree 0 ∧ 3 ≤ T.degree 1) :=
  ⟨bcv_bgnW_connected, bcv_bgnW_spanningTree_deg3⟩

-- Three pairwise unreachable vertices of the edgeless graph.
example : ∀ i j : Fin 3, i ≠ j → ¬ (⊥ : SimpleGraph (Fin 3)).Reachable (id i) (id j) :=
  bcv_sep3 (by simp) (by simp) (by simp)

-- Cluster tree data bound the coarse count.
example (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ) (h : bcv_ClusterTreeData ω L R) :
    bc61_coarseTcount ω L R ≤ boxSV_boundaryCard 2 R :=
  bcv_count_of_treeData ω L R h

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.TreeCutVertex
