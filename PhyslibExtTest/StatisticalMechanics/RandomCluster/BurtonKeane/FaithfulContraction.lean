/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.FaithfulContraction

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.FaithfulContraction`

In the plane:
* `bgf2_faithful`: reachability in the contracted graph is connectivity (the all-closed
  configuration, scale `1`, sites `0` and `(1,0)`);
* `bgf2_centre_zero` and `bgf2_idx_centre`;
* the `bao_onlyBox0` example: `bgf2_onlyBox0_hub_merged`, `bgf2_onlyBox0_not_merged` and
  `bgf2_onlyBox0_not_identified` at `L = 1`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.FaithfulContraction

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.ConfigSpace
open _root_.StatMech.Percolation _root_.StatMech.Walls MeasureTheory
open scoped NNReal

/-- The all-closed configuration of the planar lattice. -/
def closed2 : ConfigSpace (Sym2 (Site 2)) := fun _ => false

/-- In the all-closed configuration only a site is connected to itself. -/
theorem closed_connected_eq {a b : Site 2} (h : Connected 2 closed2 a b) : a = b := by
  obtain ⟨p⟩ := h
  cases p with
  | nil => rfl
  | cons hadj _ => exact absurd hadj.2 (by simp [closed2])

/-- Distinct sites have distinct clusters in the all-closed configuration. -/
theorem closed_cluster_ne {a b : Site 2} (hab : a ≠ b) :
    cluster 2 closed2 a ≠ cluster 2 closed2 b := by
  intro h
  have hb : b ∈ cluster 2 closed2 b := SimpleGraph.Reachable.refl b
  rw [← h] at hb
  exact hab (closed_connected_eq hb)

-- Contracted reachability of `0` and `(1,0)` fails in the all-closed configuration.
example : ¬ (bgf2_Gf closed2 1).Reachable (bgf2_q closed2 1 0) (bgf2_q closed2 1 ![1, 0]) :=
  fun h => by simpa using congrFun (closed_connected_eq ((bgf2_faithful closed2 1 _ _).mp h)) 0

-- The centre of index `0` is the origin, and centres have their own index.
example : bgf2_centre 3 0 = 0 ∧ bgn_idx 3 (bgf2_centre 3 ![1, -2]) = ![1, -2] :=
  ⟨bgf2_centre_zero 3, bgf2_idx_centre 3 _⟩

-- The only-box-zero configuration merges the hub but not its neighbour box.
example : bgf2_IndexAllOpen (bao_onlyBox0 1) 1 0 ∧
    ¬ bgf2_IndexAllOpen (bao_onlyBox0 1) 1 (bc57_pt 1 0) :=
  ⟨bgf2_onlyBox0_hub_merged, bgf2_onlyBox0_not_merged le_rfl⟩

-- Two sites of the neighbour box are not identified.
example : bgf2_q (bao_onlyBox0 1) 1 (bc57_pt (2 * ((1 : ℕ) : ℤ) + 1) 0)
    ≠ bgf2_q (bao_onlyBox0 1) 1 (bc57_pt (2 * ((1 : ℕ) : ℤ) + 1) 1) :=
  bgf2_onlyBox0_not_identified le_rfl


/-! ## Diagnostics moved from the production module -/

-- The `#check` / `#print axioms` commands below were moved here from
-- `StatisticalMechanics/RandomCluster/BurtonKeane/FaithfulContraction.lean`: diagnostics belong in tests, not in production modules.
#check @bgf2_boxCentre_connected
#check @bgf2_indexAllOpen_connected
#check @bgf2_Gf
#check @bgf2_faithful
#check @bgf2_cut_connected_of_reach_aux
#check @bgf2_trif_separation
#check @StatMech.Walls.bcv_trif_degree_ge_three
#check @bgf2_onlyBox0_not_merged
#check @bgf2_onlyBox0_not_identified
#check @bgf2_onlyBox0_box_connected
#check @bgf2_status
#print axioms StatMech.Walls.bgf2_boxCentre_connected
#print axioms StatMech.Walls.bgf2_faithful
#print axioms StatMech.Walls.bgf2_cut_connected_of_reach_aux
#print axioms StatMech.Walls.bgf2_trif_separation
#print axioms StatMech.Walls.bcv_trif_degree_ge_three
#print axioms StatMech.Walls.bgf2_onlyBox0_not_merged
#print axioms StatMech.Walls.bgf2_onlyBox0_not_identified

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.FaithfulContraction
