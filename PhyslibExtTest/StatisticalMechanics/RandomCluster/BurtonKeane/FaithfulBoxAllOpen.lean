/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.FaithfulBoxAllOpen

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.FaithfulBoxAllOpen`

In the plane:
* `bff_genuine_trif_with_non_allOpen_box` at `L = 3` (upper lines);
* `bff_upperLines_box_edge_closed`;
* `bff_BoxAllOpen` is satisfiable: the all-open configuration, where `bff_allOpen_box_connected`
  connects the origin to the corner `(1, 1)`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.FaithfulBoxAllOpen

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.ConfigSpace
open _root_.StatMech.Percolation _root_.StatMech.Walls MeasureTheory
open scoped NNReal

/-- The all-open configuration of the planar lattice. -/
def open2 : ConfigSpace (Sym2 (Site 2)) := fun _ => true

-- The upper lines have a genuine trifurcation whose box is not fully open.
example : bc67_IsGnTrifurcation bc60_upperLines 3 (0 : Site 2) ∧
    ¬ bff_BoxAllOpen bc60_upperLines 3 :=
  bff_genuine_trif_with_non_allOpen_box le_rfl

-- The upper lines close the edge `(0,0)–(1,0)`.
example : bc60_upperLines s(bc57_pt 0 0, bc57_pt 1 0) = false :=
  bff_upperLines_box_edge_closed

-- In the all-open configuration the box is fully open, so its sites are connected.
example : Connected 2 open2 0 ![1, 1] :=
  bff_allOpen_box_connected (n := 1) (fun _ _ => rfl) (by simp [box])
    (by simp [box, Fin.forall_fin_two])


/-! ## Diagnostics moved from the production module -/

-- The `#check` / `#print axioms` commands below were moved here from
-- `StatisticalMechanics/RandomCluster/BurtonKeane/FaithfulBoxAllOpen.lean`: diagnostics belong in tests, not in production modules.
#check @bff_allOpen_box_connected
#check @bff_upperLines_box_not_allOpen
#check @bff_genuine_trif_with_non_allOpen_box
#print axioms bff_genuine_trif_with_non_allOpen_box
#print axioms bff_allOpen_box_connected
#print axioms bff_upperLines_box_not_allOpen

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.FaithfulBoxAllOpen
