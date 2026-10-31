/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.RaysInTree

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.RaysInTree`

* the seven-vertex two-hub tree: `bri_twoHub_witness` (a tree with hubs `0`, `1` of degree `3`) and
  `bri_twoHub_count`, plus `bri_twoHub.degree 4 = 2` by `decide`;
* `bri_union_le_acyclic`: a union of subgraphs of the path on `Fin 2` is acyclic;
* `bri_rayGraph_le` in conditional form.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.RaysInTree

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.Percolation _root_.StatMech.Walls

-- The two-hub tree and its hub degrees.
example : bri_twoHub.IsTree ∧ bri_twoHub.degree 0 = 3 ∧ bri_twoHub.degree 1 = 3 :=
  ⟨bri_twoHub_witness.1, bri_twoHub_witness.2.2.1, bri_twoHub_witness.2.2.2.1⟩

-- Hub and leaf counts of the two-hub tree.
example : bri_twoHub.degree 4 = 2 ∧
    ({0, 1} : Finset (Fin 7)).card ≤ ({2, 3, 5, 6} : Finset (Fin 7)).card :=
  ⟨by decide, bri_twoHub_count⟩

-- A union of subgraphs of a tree is acyclic.
example : (⨆ i : Bool, if i then SimpleGraph.pathGraph 2 else ⊥).IsAcyclic :=
  bri_union_le_acyclic (SimpleGraph.isTree_pathGraph_add_one 1) _ fun i => by
    cases i <;> simp

-- A ray along a graph spans a subgraph of it.
example {V : Type*} (T : SimpleGraph V) (r : ℕ → V) (N : ℕ) (h : ∀ k, T.Adj (r k) (r (k + 1))) :
    bri_rayGraph r N ≤ T :=
  bri_rayGraph_le T r N h

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.RaysInTree
