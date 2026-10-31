/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.TriHex.FKStarTriangle

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.TriHex.FKStarTriangle`

Instance: `q = 4`, triangle odds `(1, 1, 1)` (on the critical surface `1 + 3 - 4 = 0`), star odds
`(4, 4, 4)` (`1 * 4 = 4`):
* the partitions evaluate to `triangle = 8`, `star = 128`, matching
  `triHexFK_terminalPartition_identity` (`1 * 128 = 4² * 8`);
* `triangleFKTerminalProbability 1 1 1 together = 1/2` by evaluation;
* `triHexFK_terminalLaw_eq` identifies the star and triangle terminal laws on the instance;
* `triangleFKTerminalProbability_sum_eq_one` at odds `(1, 1, 1)`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.TriHex.FKStarTriangle

open _root_.StatMech.FK.PeriodicPlanar _root_.StatMech.FK.TriHex

/-- The triangle odds `(1, 1, 1)` are critical at `q = 4`. -/
theorem surface_four : triangularFKCriticalSurface 4 1 1 1 = 0 := by
  norm_num [triangularFKCriticalSurface]

-- Partition values and the partition identity on the instance.
example : triangleFKTerminalPartition 1 1 1 = 8 ∧ starFKTerminalPartition 4 4 4 4 = 128 ∧
    (1 * 1 * 1) * starFKTerminalPartition 4 4 4 4 = 4 ^ 2 * triangleFKTerminalPartition 1 1 1 := by
  refine ⟨?_, ?_, triHexFK_terminalPartition_identity (by norm_num) (by norm_num)
    (by norm_num) surface_four⟩
  · rw [triangleFKTerminalPartition_eq]
    norm_num
  · rw [starFKTerminalPartition_eq]
    norm_num

-- The triangle connects all three terminals with probability `4 / 8`.
example : triangleFKTerminalProbability 1 1 1 .together = 1 / 2 := by
  rw [triangleFKTerminalProbability, triangleFKTerminalPartition_eq]
  norm_num [triangleFKTerminalWeight]

-- The star–triangle transformation preserves the terminal law.
example : starFKTerminalProbability 4 4 4 4 = triangleFKTerminalProbability 1 1 1 :=
  triHexFK_terminalLaw_eq (by norm_num) one_pos one_pos one_pos (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) surface_four

-- The triangle terminal law is a probability vector.
example : (∑ c, triangleFKTerminalProbability 1 1 1 c) = 1 :=
  triangleFKTerminalProbability_sum_eq_one one_pos one_pos one_pos

end PhyslibExtTest.StatisticalMechanics.RandomCluster.TriHex.FKStarTriangle
