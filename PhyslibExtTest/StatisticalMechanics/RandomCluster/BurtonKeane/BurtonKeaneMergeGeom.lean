/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.BurtonKeaneMergeGeom

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.BurtonKeaneMergeGeom`

* `twoMeetBox_subset_mergeWitness` at explicit sizes;
* `iEqLevel_subset_iUnion_twoMeetBox` at `k = 2`;
* `hmergeGeom_discharged` and `burton_keane_uniqueness_full` checked by type.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.BurtonKeaneMergeGeom

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.ConfigSpace
open _root_.StatMech.Percolation

-- Two clusters meeting a box give a merge witness.
example : twoMeetBox 2 3 2 ⊆ MergeWitness 2 (boxEdges 2 3) 2 :=
  twoMeetBox_subset_mergeWitness 3 2

-- Exactly two infinite clusters meet some box.
example : {ω : ConfigSpace (Sym2 (Site 2)) | numInfiniteClusters 2 ω = 2} ⊆
    ⋃ n, twoMeetBox 2 n 2 :=
  iEqLevel_subset_iUnion_twoMeetBox le_rfl

-- The merge geometry and the full uniqueness theorem, by type.
example := @hmergeGeom_discharged
example := @burton_keane_uniqueness_full

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.BurtonKeaneMergeGeom
