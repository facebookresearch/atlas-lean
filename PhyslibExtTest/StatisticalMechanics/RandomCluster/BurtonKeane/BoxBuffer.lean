/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.BoxBuffer

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.BoxBuffer`

* `bc76_yBuf_box_disjoint` and `bc76_yBuf_ne_zero` at `L = 3`;
* `bc76_buffer_insufficient` at `L = 3`: the upper-lines configuration shows a buffer between
  disjoint boxes is not enough;
* `bc76_bufferFiber_boxes_disjoint` in conditional form.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.BoxBuffer

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.ConfigSpace
open _root_.StatMech.Percolation _root_.StatMech.Walls

-- The buffer box is disjoint from the origin box and its centre is not the origin.
example : Disjoint (bc61_boxAround 2 3 (0 : Site 2)) (bc61_boxAround 2 3 (bc76_yBuf 3)) :=
  bc76_yBuf_box_disjoint 3
example : bc76_yBuf 3 ≠ (0 : Site 2) := bc76_yBuf_ne_zero 3

-- The buffer is insufficient (explicit upper-lines configuration).
example := bc76_buffer_insufficient (L := 3) le_rfl

-- Equal buffer residues of distinct centres give disjoint boxes.
example {d L : ℕ} {y y' : Site d} (hres : bc76_bufferResVec L y = bc76_bufferResVec L y')
    (hne : y ≠ y') : Disjoint (bc61_boxAround d L y) (bc61_boxAround d L y') :=
  bc76_bufferFiber_boxes_disjoint hres hne

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.BoxBuffer
