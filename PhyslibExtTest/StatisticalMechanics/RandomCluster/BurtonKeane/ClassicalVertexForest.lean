/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ClassicalVertexForest

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ClassicalVertexForest`

* `bkg_deleteVertex_adj`: deleting a vertex removes its edges (complete graph on `Fin 3`);
* `bkg_acyclic_of_singleVertexCut` applied to the empty subgraph of the complete graph;
* `bkg_reachable_eq_of_edgeless` for the empty graph;
* `bkg_coarseTcount_of_classical` in conditional form.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.ClassicalVertexForest

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.ConfigSpace
open _root_.StatMech.Percolation _root_.StatMech.Walls

-- After deleting `1` from the triangle, `0` and `1` are not adjacent.
example : ¬ (bkg_deleteVertex (⊤ : SimpleGraph (Fin 3)) 1).Adj 0 1 := by simp

-- The single-vertex-cut criterion on the empty subgraph of the triangle.
example : (⊥ : SimpleGraph (Fin 3)).IsAcyclic :=
  bkg_acyclic_of_singleVertexCut ⊤ ⊥ bot_le fun _ _ _ h => h.elim

-- In an edgeless graph, reachable vertices are equal.
example {a b : Fin 3} (h : (⊥ : SimpleGraph (Fin 3)).Reachable a b) : a = b :=
  bkg_reachable_eq_of_edgeless (fun _ _ h => h) h

-- Classical forest data give the coarse count.
example {d : ℕ} (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (h : bkg_ClassicalForestData ω L R) :
    bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R :=
  bkg_coarseTcount_of_classical ω L R h

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.ClassicalVertexForest
