/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ClassicalForestData

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ClassicalForestData`

* `bfa_singleVertexCut_of_acyclic` on the path graph on `Fin 3`: deleting the middle vertex
  separates its two neighbours;
* `bfa_classical_iff_bc69` in conditional form;
* `bfa_bk_of_classicalForest` checked by type.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.ClassicalForestData

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.ConfigSpace
open _root_.StatMech.Percolation _root_.StatMech.Walls

-- Deleting the middle vertex of the path `0 - 1 - 2` separates `0` and `2`.
example : ¬ (bkg_deleteVertex (SimpleGraph.pathGraph 3) 1).Reachable 0 2 :=
  bfa_singleVertexCut_of_acyclic _ (SimpleGraph.isAcyclic_pathGraph 3) 1 0 2 (by decide)
    (by decide) (by decide)

-- Classical forest data are the global forest.
example {d : ℕ} (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (h : bc69_Gn_globalForest ω L R) :
    bkg_ClassicalForestData ω L R :=
  (bfa_classical_iff_bc69 ω L R).mpr h

-- The Bernoulli Burton–Keane route from classical forest data, by type.
example := @bfa_bk_of_classicalForest

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.ClassicalForestData
