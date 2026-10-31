/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.ApproximatePreference

/-!
# Tests for `Sheffield.ApproximatePreference`

Module under test: `Sheffield.ApproximatePreference` in
`PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar`.

On the `2 × 2` grid, with `rowInd` (`1` on the bottom row, `0` above) and `colInd` (`1` on the
left column):
* `exists_common_weak_approximate_preference_grid_witness` with `ε = 0`, bottom `rowInd`, top
  `1 - rowInd`, left `colInd`, right `1 - colInd`;
* `rectangleEndpointPreferenceError` vanishes for these exact preferences;
* `rectangleEndpointPreferenceError_tendsto_zero` for constant-`1` boundary probabilities;
* `crossing_max_tendsto_one_of_approxPreferredSide_root_branches` on constant sequences.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield
namespace ApproximatePreference

open _root_.StatMech.FK.PeriodicPlanar _root_.StatMech.Lattice Filter

/-- `1` on the bottom row of the `2 × 2` grid, `0` elsewhere. -/
noncomputable def rowInd (v : PreferenceGridVertex 1 1) : ℝ := if v.2 = 0 then 1 else 0

/-- `1` on the left column of the `2 × 2` grid, `0` elsewhere. -/
noncomputable def colInd (v : PreferenceGridVertex 1 1) : ℝ := if v.1 = 0 then 1 else 0

-- An exact (`ε = 0`) preference witness.
example : ∃ x xV xH : PreferenceGridVertex 1 1,
    1 - rowInd x ≤ rowInd x + 0 ∧ 1 - colInd x ≤ colInd x + 0 ∧
    KingAdj (preferenceGridSite x) (preferenceGridSite xV) ∧
    rowInd xV ≤ 1 - rowInd xV + 0 ∧
    KingAdj (preferenceGridSite x) (preferenceGridSite xH) ∧
    colInd xH ≤ 1 - colInd xH + 0 :=
  exists_common_weak_approximate_preference_grid_witness one_pos one_pos 0 le_rfl
    rowInd (fun v => 1 - rowInd v) colInd (fun v => 1 - colInd v)
    (fun i => by norm_num [rowInd]) (fun i => by norm_num [rowInd])
    (fun j => by norm_num [colInd]) (fun j => by norm_num [colInd])

-- Exact boundary preferences have zero endpoint error.
example : rectangleEndpointPreferenceError rowInd (fun v => 1 - rowInd v) colInd
    (fun v => 1 - colInd v) = 0 := by
  simp [rectangleEndpointPreferenceError, rowInd, colInd]

-- Constant-`1` boundary probabilities give vanishing endpoint error.
example : Tendsto (fun _ : ℕ => rectangleEndpointPreferenceError (n := 1) (m := 1)
    (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1)) atTop (nhds 0) :=
  rectangleEndpointPreferenceError_tendsto_zero (fun _ _ => 1) (fun _ _ => 1) (fun _ _ => 1)
    (fun _ _ => 1) (fun _ => tendsto_const_nhds) (fun _ => tendsto_const_nhds)
    (fun _ => tendsto_const_nhds) (fun _ => tendsto_const_nhds)
    (fun _ _ => le_rfl) (fun _ _ => le_rfl) (fun _ _ => le_rfl) (fun _ _ => le_rfl)

-- The crossing dichotomy on constant sequences (`root = A = H = C = 1`, errors `0`).
example : Tendsto (fun N : ℕ => max ((fun _ => (1 : ℝ)) N) ((fun _ => (1 : ℝ)) N))
    atTop (nhds 1) :=
  crossing_max_tendsto_one_of_approxPreferredSide_root_branches (fun _ => 1) (fun _ => 1)
    (fun _ => 1) (fun _ => 1) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 1) (fun _ => 1)
    tendsto_const_nhds (fun _ => by norm_num) (fun _ => le_rfl) tendsto_const_nhds
    tendsto_const_nhds tendsto_const_nhds tendsto_const_nhds tendsto_const_nhds
    (fun _ => Or.inl (by norm_num)) (fun _ => le_rfl) (fun _ => le_rfl)

end ApproximatePreference
end PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield
