/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.PreferenceInterface

/-!
# Tests for `Sheffield.PreferenceInterface`

Module under test: `Sheffield.PreferenceInterface` in
`PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar`.

On the `2 × 2` grid (`n = m = 1`) with the coloring `rowZero` (true on the bottom row, false on
the top row):
* `reachable_of_only_two_odd_degree` on the complete graph on `Fin 2` (both vertices odd);
* `preferenceInterface_left_reachable_right` for `rowZero`;
* `exists_preference_witness_of_grid_boundary` for `rowZero` and `Y` the column `x = 0`;
* `preferenceGridBoundary_reachable_left_right_of_flagCrossing` elaborates (check-only).
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield
namespace PreferenceInterface

open _root_.StatMech.FK.PeriodicPlanar _root_.StatMech.Lattice

/-- The coloring of the `2 × 2` grid that is true exactly on the bottom row. -/
def rowZero (v : PreferenceGridVertex 1 1) : Bool := decide (v.2 = 0)

-- The two vertices of the complete graph on `Fin 2` are its only odd-degree vertices.
example : (⊤ : SimpleGraph (Fin 2)).Reachable 0 1 :=
  reachable_of_only_two_odd_degree ⊤ 0 1 (by decide) (fun v _ => by fin_cases v <;> simp)

-- The interface graph of `rowZero` joins its left and right ends.
example : (preferenceInterfaceGraph rowZero).Reachable (.left) (.right) :=
  preferenceInterface_left_reachable_right rowZero one_pos true false
    (fun i => by simp [rowZero]) (fun i => by simp [rowZero]) (by decide)

-- A preference witness for `rowZero` and the column `{z | z 0 = 0}`.
example : ∃ x ∈ preferenceGridRectangle 1 1,
    x ∈ preferenceGridTrueSet rowZero ∧ x ∈ {z : Site 2 | z 0 = 0} ∧
      (∃ x' ∈ preferenceGridRectangle 1 1, KingAdj x x' ∧
        x' ∉ preferenceGridTrueSet rowZero) ∧
      (∃ x'' ∈ preferenceGridRectangle 1 1, KingAdj x x'' ∧
        x'' ∉ {z : Site 2 | z 0 = 0}) :=
  exists_preference_witness_of_grid_boundary rowZero one_pos (fun i => by simp [rowZero])
    (fun i => by simp [rowZero]) {z : Site 2 | z 0 = 0}
    (fun x hx => by
      change preferenceGridSite x.val 0 = 0
      simp [preferenceGridSite, hx])
    (fun x hx => by
      change ¬ preferenceGridSite x.val 0 = 0
      simp [preferenceGridSite, hx])

-- `preferenceGridBoundary_reachable_left_right_of_flagCrossing` elaborates.
example := @preferenceGridBoundary_reachable_left_right_of_flagCrossing

end PreferenceInterface
end PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield
