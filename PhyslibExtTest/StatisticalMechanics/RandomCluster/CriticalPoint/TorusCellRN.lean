/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.TorusCellRN

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.TorusCellRN`

On the `3 × 3` torus with the all-closed configuration:
* `torusAmbientDefect_classified` (defect in `{0, 1, 2}`);
* `torusAmbientFKWeight_pos` and `torusAmbientProbability_sum_one` at `p = 1/2`, `q = 2`;
* `torusAmbientFKWeight_selfDual_relation` and `torusAmbientProbability_selfDual_ratio_mem` at
  `q = 2`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.CriticalPoint.TorusCellRN

open _root_.StatMech _root_.StatMech.BeffaraDC _root_.StatMech.Onsager

instance : Fact (2 < 3) := ⟨by norm_num⟩

/-- The all-closed torus configuration. -/
def closed3 : TorusAmbientConfig 3 := fun _ => false

-- The defect is `0`, `1` or `2`.
example := torusAmbientDefect_classified 3 closed3

-- Positive weight.
example : 0 < torusAmbientFKWeight 3 (1 / 2) 2 closed3 :=
  torusAmbientFKWeight_pos 3 closed3 (by norm_num) (by norm_num) (by norm_num)

-- The torus probabilities sum to `1`.
example : ∑ omega : TorusAmbientConfig 3, torusAmbientProbability 3 (1 / 2) 2 omega = 1 :=
  torusAmbientProbability_sum_one 3 (by norm_num) (by norm_num) (by norm_num)

-- The self-dual weight relation at `q = 2`.
example := torusAmbientFKWeight_selfDual_relation 3 closed3 (q := 2) (by norm_num)

-- The self-dual probability ratio lies in `[1/2, 2]`.
example := torusAmbientProbability_selfDual_ratio_mem 3 closed3 (q := 2) (by norm_num)

end PhyslibExtTest.StatisticalMechanics.RandomCluster.CriticalPoint.TorusCellRN
