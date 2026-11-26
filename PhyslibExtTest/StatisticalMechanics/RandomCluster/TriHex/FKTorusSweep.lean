/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.TriHex.FKTorusSweep

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.TriHex.FKTorusSweep`

* `triHexDirectionOdds` and `starFKIsolatedCenterFactor` evaluate on concrete inputs;
* `triangularTorusActiveTwoPointIndicator` is `1` on the diagonal (every site reaches itself);
* `triHexFK_torus_activeTwoPointRatio_eq` on the `3 × 3` torus at `q = 4` with constant edge
  probabilities `1/2` (triangle odds `1`) and `4/5` (star odds `4`).
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.TriHex.FKTorusSweep

open _root_.StatMech.FK.PeriodicPlanar _root_.StatMech.FK.TriHex _root_.StatMech.FK

/-- The `3 × 3` torus is admissible. -/
local instance fact_two_lt_three : Fact (2 < 3) := ⟨by norm_num⟩

/-- Constant direction odds. -/
theorem directionOdds_const (y : ℝ) (i : Fin 3) : triHexDirectionOdds y y y i = y := by
  fin_cases i <;> rfl

-- Direction odds and the isolated-center factor.
example : triHexDirectionOdds 1 2 3 1 = 2 ∧ starFKIsolatedCenterFactor 4 (false, false, false) = 4 ∧
    starFKIsolatedCenterFactor 4 (true, false, false) = 1 := by
  refine ⟨rfl, ?_, ?_⟩ <;> simp [starFKIsolatedCenterFactor]

-- Every site is connected to itself.
example (x : TorusSite 3) (omega : _root_.StatMech.ConfigSpace (triangularTorusGraph 3).edgeSet) :
    triangularTorusActiveTwoPointIndicator 3 x x omega = 1 := by
  simp [triangularTorusActiveTwoPointIndicator]

-- Star–triangle invariance of the two-point ratio on the `3 × 3` torus.
example (x y : TorusSite 3) :
    activeNumer (hexagonalTorusGraph 3) (fun _ => 4 / 5) 4
        (hexagonalTorusActiveWhiteTwoPointIndicator 3 x y) /
        activeZ (hexagonalTorusGraph 3) (fun _ => 4 / 5) 4 =
      activeNumer (triangularTorusGraph 3) (fun _ => 1 / 2) 4
        (triangularTorusActiveTwoPointIndicator 3 x y) /
        activeZ (triangularTorusGraph 3) (fun _ => 1 / 2) 4 :=
  triHexFK_torus_activeTwoPointRatio_eq 3 (fun _ => 1 / 2) (fun _ => 4 / 5)
    (y0 := 1) (y1 := 1) (y2 := 1) (y0Star := 4) (y1Star := 4) (y2Star := 4)
    (by norm_num) (by norm_num) (fun _ => by norm_num) (fun _ => by norm_num)
    (fun e => by rw [triangularTorusSweepEdgeOdds, directionOdds_const]; norm_num)
    (fun e => by rw [hexagonalTorusSweepEdgeOdds, directionOdds_const]; norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [triangularFKCriticalSurface]) x y

end PhyslibExtTest.StatisticalMechanics.RandomCluster.TriHex.FKTorusSweep
