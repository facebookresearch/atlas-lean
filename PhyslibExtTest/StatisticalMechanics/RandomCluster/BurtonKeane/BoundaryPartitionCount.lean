/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.BoundaryPartitionCount

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.BoundaryPartitionCount`

* `bpt_cut_ground_sets_differ` at `L = 1`;
* `bpt_sameTrif_classes_laminar` for the all-open configuration of `ℤ²`;
* `bpt_trif_three_classes_disjoint` checked by type.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.BoundaryPartitionCount

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.ConfigSpace
open _root_.StatMech.Percolation _root_.StatMech.Walls

-- Different trifurcations cut different ground sets.
example := bpt_cut_ground_sets_differ 1 le_rfl

-- Boundary classes of one trifurcation are laminar (all-open configuration).
example (a b : Site 2) : bpt_boundaryClass (fun _ => true) 1 1 0 a =
      bpt_boundaryClass (fun _ => true) 1 1 0 b ∨
    Disjoint (bpt_boundaryClass (fun _ => true) 1 1 0 a)
      (bpt_boundaryClass (fun _ => true) 1 1 0 b) :=
  bpt_sameTrif_classes_laminar _ 1 1 0 a b

-- The three classes of a trifurcation are disjoint, by type.
example := @bpt_trif_three_classes_disjoint

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.BoundaryPartitionCount
