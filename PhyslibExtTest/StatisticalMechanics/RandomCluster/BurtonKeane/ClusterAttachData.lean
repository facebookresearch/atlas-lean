/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ClusterAttachData

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ClusterAttachData`

* `tex_threeDistinctInfinite_of_threeMeetBox` in conditional form;
* `tex_disjointRouting_of_box` and `tex_boxMengerAttachment_of_boxAttachData` in conditional
  form;
* `tex_attachData_of_neighbour_witnesses` checked by type.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.ClusterAttachData

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.ConfigSpace
open _root_.StatMech.Percolation

-- Three clusters meeting a box are distinct and infinite.
example {d n : ℕ} {ω : ConfigSpace (Sym2 (Site d))} (hω : ω ∈ threeMeetBox d n) :
    tex_ThreeDistinctInfinite ω :=
  tex_threeDistinctInfinite_of_threeMeetBox hω

-- Box attach data give disjoint routing and the Menger attachment.
example {d n : ℕ} (h : tex_BoxAttachData d n) : hrHD_DisjointRouting d n :=
  tex_disjointRouting_of_box h
example {d n : ℕ} (h : tex_BoxAttachData d n) : bmm_BoxMengerAttachment d n :=
  tex_boxMengerAttachment_of_boxAttachData h

-- Attach data from neighbour witnesses, by type.
example := @tex_attachData_of_neighbour_witnesses

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.ClusterAttachData
