/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.TriHex.TorusPressureDuality

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.TriHex.TorusPressureDuality`

* `triHexTorusPrimalPartitionSum_pos` on the torus of side `3` at `p = 1 / 2`, `q = 2`;
* at `q = 1` the pressure duality residual on the torus of side `3` is exactly `0` (from
  `triHexTorusPressureDualityResidual_eq_partitionCorrection` and the log bounds);
* `triHexTorusPressureDualityResidual_tendsto_zero` at `p = 1 / 2`, `q = 2`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.TriHex.TorusPressureDuality

open _root_.StatMech.FK.PeriodicPlanar

instance : Fact (2 < 3) := ⟨by norm_num⟩

-- The primal torus partition function is positive.
example : 0 < triHexTorusPrimalPartitionSum 3 (1 / 2) 2 :=
  triHexTorusPrimalPartitionSum_pos 3 (by norm_num) (by norm_num) (by norm_num)

-- At `q = 1` the residual vanishes exactly.
example : triHexTorusPressureDualityResidual 3 (1 / 2) 1 = 0 := by
  have h := triHexTorus_partitionCorrection_log_bounds 3 (p := 1 / 2) (q := 1)
    (by norm_num) (by norm_num) le_rfl
  rw [Real.log_one, mul_zero] at h
  rw [triHexTorusPressureDualityResidual_eq_partitionCorrection 3 (by norm_num) (by norm_num)
    le_rfl, le_antisymm h.2 h.1, zero_div]

-- Pressure duality in the thermodynamic limit.
example := triHexTorusPressureDualityResidual_tendsto_zero (p := 1 / 2) (q := 2)
  (by norm_num) (by norm_num) (by norm_num)

end PhyslibExtTest.StatisticalMechanics.RandomCluster.TriHex.TorusPressureDuality
