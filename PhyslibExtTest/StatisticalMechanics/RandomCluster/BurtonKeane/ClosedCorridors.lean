/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ClosedCorridors

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ClosedCorridors`

* `bpt2_Ext_nonempty` and `bpt2_omega_mem_precursor`: the explicit configuration `bpt2_omega`
  witnesses the extension event and the neighbour precursor;
* `bpt2_disjoint_S₁_S₂`: the explicit regions are disjoint;
* `bpt2_closeI_le`: closing edges lowers a configuration (all-open instance).
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.ClosedCorridors

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.ConfigSpace
open _root_.StatMech.Percolation _root_.StatMech.Walls

-- The extension event is nonempty.
example := bpt2_Ext_nonempty

-- The explicit configuration lies in the neighbour precursor.
example : bpt2_omega ∈ NeighborTrifPrecursor 2 bmf_a₁ bmf_a₂ bmf_a₃ := bpt2_omega_mem_precursor

-- The first two regions are disjoint.
example : Disjoint bpt2_S₁ bpt2_S₂ := bpt2_disjoint_S₁_S₂

-- Closing the edges of `I` lowers the configuration.
example (I : Finset (Sym2 (Site 2))) : bpt2_closeI I (fun _ => true) ≤ fun _ => true :=
  bpt2_closeI_le I _

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.ClosedCorridors
