/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.TriHex.FKSimultaneousStarTriangle

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.TriHex.FKSimultaneousStarTriangle`

* local connectivities: two open triangle sides join all terminals, one open star spoke joins
  none, and the all-closed star carries the isolated-center weight `q`;
* `triangleFKLocalOddsWeight_fiber`: the `together` fiber of the unit-odds triangle has weight `4`;
* `ThreeTerminalConnectivity.Connects`: `pair01` connects `1` to `0` but not `0` to `2`;
* `triHexFK_globalSweepRatio_eq` on two cells (`ι = Fin 2`) at `q = 4`, odds `1` / `4`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.TriHex.FKSimultaneousStarTriangle

open _root_.StatMech.FK.PeriodicPlanar _root_.StatMech.FK.TriHex

-- Local connectivities and the isolated-center weight.
example : triangleFKLocalConnectivity (true, true, false) = .together ∧
    starFKLocalConnectivity (true, false, false) = .separate ∧
    starFKLocalOddsWeight 4 1 1 1 (false, false, false) = 4 :=
  ⟨rfl, rfl, rfl⟩

-- The `together` fiber of the unit-odds triangle: `1 + 1 + 1 + 1 = 4`.
example : (∑ omega : _root_.StatMech.Universality.LocalConfig,
      if triangleFKLocalConnectivity omega = .together then
        triangleFKLocalOddsWeight 1 1 1 omega else 0) = 4 := by
  rw [triangleFKLocalOddsWeight_fiber]
  norm_num [triangleFKTerminalWeight]

-- `pair01` connects terminals `1` and `0` and not `0` and `2`.
example : ThreeTerminalConnectivity.pair01.Connects 1 0 ∧
    ¬ ThreeTerminalConnectivity.pair01.Connects 0 2 := by
  refine ⟨Or.inr (Or.inr ⟨rfl, rfl⟩), ?_⟩
  rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩) <;> simp_all

-- Global star–triangle invariance on two cells.
example (external observable : (Fin 2 → ThreeTerminalConnectivity) → ℝ) :
    starFKGlobalSweepRatio 4 4 4 4 external observable =
      triangleFKGlobalSweepRatio 1 1 1 external observable :=
  triHexFK_globalSweepRatio_eq (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num [triangularFKCriticalSurface]) external observable

end PhyslibExtTest.StatisticalMechanics.RandomCluster.TriHex.FKSimultaneousStarTriangle
