/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.TriHex.HexagonalSharpnessThreshold

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.TriHex.HexagonalSharpnessThreshold`

* `hexagonalSharpConstant_le_one` / `one_le_inv_hexagonalSharpConstant` at `β₀ = 1`;
* `hexagonalThresholdTheta_of_pos` and `hexagonalThresholdTheta_nonneg` at `n = 1`, `q = 1`,
  `β = β₀ = 1`;
* `hexagonalThresholdSig_of_nonpos`: at `β = 0` the threshold sum equals `1 / c(β₀)`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.TriHex.HexagonalSharpnessThreshold

open _root_.StatMech.FK.PeriodicPlanar _root_.StatMech.OSSS

-- The sharpness constant is at most `1`, so its inverse is at least `1`.
example : hexagonalSharpConstant 1 ≤ 1 ∧ 1 ≤ 1 / hexagonalSharpConstant 1 :=
  ⟨hexagonalSharpConstant_le_one 1 zero_le_one, one_le_inv_hexagonalSharpConstant 1 zero_le_one⟩

-- For `β > 0` the threshold function is the normalized crossing probability, which is `≥ 0`.
example : hexagonalThresholdTheta 1 1 1 1 = hexagonalNormalizedTheta 1 1 1 1 ∧
    0 ≤ hexagonalThresholdTheta 1 1 1 1 :=
  ⟨hexagonalThresholdTheta_of_pos 1 1 1 1 one_pos, hexagonalThresholdTheta_nonneg 1 1 1 1 le_rfl⟩

-- At `β = 0` the threshold sum is the constant `1 / c(β₀)`.
example : IntegrationSubcritical.Sig (hexagonalThresholdTheta 1 1) 1 0 =
    1 / hexagonalSharpConstant 1 :=
  hexagonalThresholdSig_of_nonpos 1 le_rfl 1 1 0 le_rfl

end PhyslibExtTest.StatisticalMechanics.RandomCluster.TriHex.HexagonalSharpnessThreshold
