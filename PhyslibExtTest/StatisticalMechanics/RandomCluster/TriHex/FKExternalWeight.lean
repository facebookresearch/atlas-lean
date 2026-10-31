/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.TriHex.FKExternalWeight

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.TriHex.FKExternalWeight`

Instance: `q = 4`, triangle odds `(1, 1, 1)`, star odds `(4, 4, 4)`:
* with the trivial environment `external = 1` the weighted sums are the partitions (`8` and `128`);
* `triHexFK_terminalWeightedSum_identity` for an arbitrary environment;
* `triHexFK_terminalWeightedRatio_eq`: star and triangle expectations of any observable agree.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.TriHex.FKExternalWeight

open _root_.StatMech.FK.PeriodicPlanar _root_.StatMech.FK.TriHex

/-- The triangle odds `(1, 1, 1)` are critical at `q = 4`. -/
theorem surface_four : triangularFKCriticalSurface 4 1 1 1 = 0 := by
  norm_num [triangularFKCriticalSurface]

-- The trivial environment recovers the triangle partition `8`.
example : triangleFKTerminalWeightedSum 1 1 1 (fun _ => 1) = 8 := by
  have h := triangleFKTerminalPartition_eq 1 1 1
  rw [triangleFKTerminalPartition] at h
  rw [triangleFKTerminalWeightedSum]
  simp only [one_mul]
  rw [h]
  norm_num

-- The weighted-sum identity for an arbitrary environment.
example (external : ThreeTerminalConnectivity → ℝ) :
    (1 * 1 * 1) * starFKTerminalWeightedSum 4 4 4 4 external =
      4 ^ 2 * triangleFKTerminalWeightedSum 1 1 1 external :=
  triHexFK_terminalWeightedSum_identity (by norm_num) (by norm_num) (by norm_num) surface_four
    external

-- Star and triangle expectations agree for every environment and observable.
example (external observable : ThreeTerminalConnectivity → ℝ) :
    starFKTerminalWeightedRatio 4 4 4 4 external observable =
      triangleFKTerminalWeightedRatio 1 1 1 external observable :=
  triHexFK_terminalWeightedRatio_eq (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) surface_four external observable

end PhyslibExtTest.StatisticalMechanics.RandomCluster.TriHex.FKExternalWeight
