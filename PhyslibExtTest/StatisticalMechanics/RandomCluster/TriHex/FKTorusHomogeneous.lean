/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.TriHex.FKTorusHomogeneous

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.TriHex.FKTorusHomogeneous`

On the `3 × 3` torus at `q = 4`, `p = 1/2` (odds `1`, a root of `y³ + 3y² - 4`):
* `triHexFK_torus_homogeneous_activeTwoPointRatio_eq`: the hexagonal two-point ratio at
  `dualParam (1/2) 4` equals the triangular one at `1/2`;
* `triHexFK_torus_homogeneous_activeSectorRatio_eq` for the constant observable `1`;
* `dualParam (1/2) 4 = 4/5` by evaluation, so the hexagonal parameter is concrete.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.TriHex.FKTorusHomogeneous

open _root_.StatMech.FK.PeriodicPlanar _root_.StatMech.FK.TriHex _root_.StatMech.FK
open _root_.StatMech.BeffaraDC

/-- The `3 × 3` torus is admissible. -/
local instance fact_two_lt_three : Fact (2 < 3) := ⟨by norm_num⟩

/-- `p = 1/2` is the triangular critical point at `q = 4`. -/
theorem crit_half : triangularFKCriticalPolynomial 4 (fkEdgeOdds (1 / 2)) = 0 := by
  norm_num [triangularFKCriticalPolynomial, fkEdgeOdds]

-- The dual parameter is `4/5`.
example : dualParam (1 / 2) 4 = 4 / 5 := by
  norm_num [dualParam]

-- Two-point ratios agree at the critical point.
example (x y : TorusSite 3) :
    activeNumer (hexagonalTorusGraph 3) (fun _ => dualParam (1 / 2) 4) 4
        (hexagonalTorusActiveWhiteTwoPointIndicator 3 x y) /
        activeZ (hexagonalTorusGraph 3) (fun _ => dualParam (1 / 2) 4) 4 =
      activeNumer (triangularTorusGraph 3) (fun _ => 1 / 2) 4
        (triangularTorusActiveTwoPointIndicator 3 x y) /
        activeZ (triangularTorusGraph 3) (fun _ => 1 / 2) 4 :=
  triHexFK_torus_homogeneous_activeTwoPointRatio_eq 3 (by norm_num) ⟨by norm_num, by norm_num⟩
    crit_half x y

-- Sector ratios agree for the constant observable.
example :
    activeNumer (hexagonalTorusGraph 3) (fun _ => dualParam (1 / 2) 4) 4
        (hexagonalTorusSectorObservable 3 (fun _ => 1)) /
        activeZ (hexagonalTorusGraph 3) (fun _ => dualParam (1 / 2) 4) 4 =
      activeNumer (triangularTorusGraph 3) (fun _ => 1 / 2) 4
        (triangularTorusSectorObservable 3 (fun _ => 1)) /
        activeZ (triangularTorusGraph 3) (fun _ => 1 / 2) 4 :=
  triHexFK_torus_homogeneous_activeSectorRatio_eq 3 (by norm_num) ⟨by norm_num, by norm_num⟩
    crit_half _

end PhyslibExtTest.StatisticalMechanics.RandomCluster.TriHex.FKTorusHomogeneous
