/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.WholeBoxOpenTrif

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.WholeBoxOpenTrif`

* instance: opening the box `B_1` reconnects `(1, 0)` and `(-1, 0)` around the origin
  (`bc58_reconnect_around_origin`), for the all-closed configuration;
* `bc58_boxOpen_not_classicalTrif`: the opened configuration has no classical trifurcation at the
  origin; likewise for the even-lines configuration (`bc58_evenLines_boxOpen_reconnect`);
* `bc58_boxOpen_edge_open` on a concrete box edge;
* the last conjunct of `bc58_status`: `bc57_evenLines ∈ threeMeetBox 2 6`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.WholeBoxOpenTrif

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.Percolation _root_.StatMech.Walls
open _root_.StatMech.ConfigSpace MeasureTheory

-- Opening `B_1` reconnects the horizontal neighbours of the origin.
example :
    Connected 2 (removeSite 0 (bc58_boxOpen 2 1 (fun _ => false))) (bc58_p 1 0) (bc58_p (-1) 0) :=
  bc58_reconnect_around_origin le_rfl _

-- So the opened box never has a classical trifurcation at the origin.
example : ¬ bc47_IsClassicalTrifurcation (bc58_boxOpen 2 1 (fun _ => false)) 0 ∧
    ¬ bc47_IsClassicalTrifurcation (bc58_boxOpen 2 2 bc57_evenLines) 0 :=
  ⟨bc58_boxOpen_not_classicalTrif le_rfl _, bc58_evenLines_boxOpen_reconnect (by norm_num)⟩

-- The edge from `(0, 0)` to `(1, 0)` is open after opening `B_1`.
example : IsOpenEdge 2 (bc58_boxOpen 2 1 (fun _ => false)) (bc58_p 0 0) (bc58_p 1 0) :=
  bc58_boxOpen_edge_open (bc58_p_mem_box (by decide) (by decide))
    (bc58_p_mem_box (by decide) (by decide)) (bc58_p_adj_horiz 0 0) _

-- The even-lines configuration lies in `threeMeetBox 2 6`.
example : bc57_evenLines ∈ threeMeetBox 2 6 :=
  (bc58_status (d := 1) le_rfl (1 / 2) (by norm_num) (by norm_num)).2.2.2

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.WholeBoxOpenTrif
