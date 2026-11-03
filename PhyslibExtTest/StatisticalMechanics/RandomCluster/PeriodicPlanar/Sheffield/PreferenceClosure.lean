/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.PreferenceClosure

/-!
# Tests for `Sheffield.PreferenceClosure`

Module under test: `Sheffield.PreferenceClosure` in
`PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar`.

* `exists_common_preference_grid_witness` on the `2 × 2` grid with the vertical coloring true on
  the bottom row and the horizontal coloring true on the left column.
* The same with the vertical coloring reversed (bottom false, top true): only distinct end colors
  are required.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield
namespace PreferenceClosure

open _root_.StatMech.FK.PeriodicPlanar _root_.StatMech.Lattice

/-- True exactly on the bottom row of the `2 × 2` grid. -/
def rowZero (v : PreferenceGridVertex 1 1) : Bool := decide (v.2 = 0)

/-- True exactly on the left column of the `2 × 2` grid. -/
def colZero (v : PreferenceGridVertex 1 1) : Bool := decide (v.1 = 0)

-- A common witness for the bottom-row and left-column colorings.
example : ∃ x : PreferenceGridVertex 1 1, rowZero x = true ∧ colZero x = true ∧
    (∃ xV : PreferenceGridVertex 1 1,
      KingAdj (preferenceGridSite x) (preferenceGridSite xV) ∧ rowZero xV = false) ∧
    (∃ xH : PreferenceGridVertex 1 1,
      KingAdj (preferenceGridSite x) (preferenceGridSite xH) ∧ colZero xH = false) :=
  exists_common_preference_grid_witness one_pos rowZero colZero true false
    (fun i => by simp [rowZero]) (fun i => by simp [rowZero]) (by decide)
    (fun j => by simp [colZero]) (fun j => by simp [colZero])

-- The vertical coloring may also be false at the bottom and true at the top.
example : ∃ x : PreferenceGridVertex 1 1, (!rowZero x) = true ∧ colZero x = true ∧
    (∃ xV : PreferenceGridVertex 1 1,
      KingAdj (preferenceGridSite x) (preferenceGridSite xV) ∧ (!rowZero xV) = false) ∧
    (∃ xH : PreferenceGridVertex 1 1,
      KingAdj (preferenceGridSite x) (preferenceGridSite xH) ∧ colZero xH = false) :=
  exists_common_preference_grid_witness one_pos (fun v => !rowZero v) colZero false true
    (fun i => by simp [rowZero]) (fun i => by simp [rowZero]) (by decide)
    (fun j => by simp [colZero]) (fun j => by simp [colZero])

end PreferenceClosure
end PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield
