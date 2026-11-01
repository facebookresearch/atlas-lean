/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.SuperCut

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.SuperCut`

* `bsc_boxCentre_zero`: the origin is a box centre;
* `bsc_ediv_zero_iff` at `L = 2`, `a = -2` (by `decide` on the right side);
* `bsc_box_isolated`: sites of the removed box have no open edge, on the all-closed configuration;
* instance: `bsc_upperLines_forward` at `L = 3` (three infinite arms from the hub of
  `bc60_upperLines` in the contracted graph).
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.SuperCut

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.Percolation _root_.StatMech.Walls
open _root_.StatMech.ConfigSpace MeasureTheory

-- The origin is a box centre.
example (L : ℕ) : bsc_IsBoxCentre L (0 : Site 2) := bsc_boxCentre_zero 2 L

-- `-2` lies in the central block of width `5`.
example : ((-2 : ℤ) + (2 : ℕ)) / (2 * ((2 : ℕ) : ℤ) + 1) = 0 :=
  bsc_ediv_zero_iff.mpr (by decide)

-- Sites of the removed box are isolated.
example (L : ℕ) (y a w : Site 2) (ha : a ∈ bc61_boxAround 2 L y) :
    ¬ (openSubgraph 2 (removeSites (bc61_boxAround 2 L y) (fun _ => false))).Adj a w :=
  bsc_box_isolated _ ha w

-- The hub of the upper-lines configuration has three infinite arms in the contracted graph.
example : ∃ w₁ w₂ w₃ : Site 2,
    (w₁ ≠ bgn_idx 3 (0 : Site 2) ∧ w₂ ≠ bgn_idx 3 (0 : Site 2) ∧ w₃ ≠ bgn_idx 3 (0 : Site 2)) ∧
    ((bgn_Gn bc60_upperLines 3).Adj (bgn_idx 3 (0 : Site 2)) w₁ ∧
     (bgn_Gn bc60_upperLines 3).Adj (bgn_idx 3 (0 : Site 2)) w₂ ∧
     (bgn_Gn bc60_upperLines 3).Adj (bgn_idx 3 (0 : Site 2)) w₃) ∧
    ((ray34_AvoidCluster (bgn_Gn bc60_upperLines 3) {bgn_idx 3 (0 : Site 2)} w₁).Infinite ∧
     (ray34_AvoidCluster (bgn_Gn bc60_upperLines 3) {bgn_idx 3 (0 : Site 2)} w₂).Infinite ∧
     (ray34_AvoidCluster (bgn_Gn bc60_upperLines 3) {bgn_idx 3 (0 : Site 2)} w₃).Infinite) :=
  bsc_upperLines_forward le_rfl


/-! ## Diagnostics moved from the production module -/

-- The `#check` / `#print axioms` commands below were moved here from
-- `StatisticalMechanics/RandomCluster/BurtonKeane/SuperCut.lean`: diagnostics belong in tests, not in production modules.
#check @bfin_SuperCutBridge
#check @bsc_boxCentre_zero
#check @bsc_hub_adj_armImage
#check @bsc_superReach_of_siteConn
#check @bsc_arm_ray_infinite
#check @bsc_siteConn_of_superReach
#check @bsc_bfin_SuperCutBridge_of_hyp
#check @bsc_upperLines_forward
#check @bsc_status
#print axioms StatMech.Walls.bsc_hub_adj_armImage
#print axioms StatMech.Walls.bsc_arm_ray_infinite
#print axioms StatMech.Walls.bsc_superReach_of_siteConn
#print axioms StatMech.Walls.bsc_siteConn_of_superReach
#print axioms StatMech.Walls.bsc_bridge_of_internalConn
#print axioms StatMech.Walls.bsc_bfin_SuperCutBridge_of_hyp
#print axioms StatMech.Walls.bsc_upperLines_forward
#print axioms StatMech.Walls.bsc_status

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.SuperCut
