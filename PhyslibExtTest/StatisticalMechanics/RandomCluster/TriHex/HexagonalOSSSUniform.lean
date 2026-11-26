/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.TriHex.HexagonalOSSSUniform

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.TriHex.HexagonalOSSSUniform`

* `hexagonalSharpConstant 0 = 1/8` by evaluation;
* `hexagonalOuterCenteredConn_zero` and `hexagonalBox_root_degree_le_six` at the root of the
  radius-`1` box (`q = 1`, `β = 1`);
* `hexagonalOuterInnerSig_pos` at `n = 1`, `q = 2`, `β = 1/2`;
* `hexagonal_outer_inner_differential_uniform` at `n = 1`, `q = 1`, `β = β₀ = 1` (all
  hypotheses concrete and satisfied).
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.TriHex.HexagonalOSSSUniform

open _root_.StatMech.FK.PeriodicPlanar

-- The sharpness constant at `β₀ = 0`.
example : hexagonalSharpConstant 0 = 1 / 8 := by
  norm_num [hexagonalSharpConstant]

-- The root is connected to its own centered shell of radius `0`, and has degree at most `6`.
example : hexagonalOuterCenteredConn 1 1 1 (hexagonalBoxRoot 1) 0 = 1 ∧
    (hexagonalBoxGraph 1).degree (hexagonalBoxRoot 1) ≤ 6 :=
  ⟨hexagonalOuterCenteredConn_zero 1 1 1 le_rfl one_pos _,
    hexagonalBox_root_degree_le_six 1 le_rfl⟩

-- The normalizing sum `Σ_n` is positive.
example : 0 < hexagonalOuterInnerSig 1 2 (1 / 2) :=
  hexagonalOuterInnerSig_pos 1 le_rfl 2 (1 / 2) (by norm_num) (by norm_num)

-- The uniform OSSS differential inequality at a concrete parameter point.
example : hexagonalSharpConstant 1 *
      (((1 : ℕ) : ℝ) / hexagonalOuterInnerSig 1 1 1 * hexagonalOuterInnerTheta 1 1 1) ≤
    hexagonalOuterInnerThetaPrime 1 1 1 :=
  hexagonal_outer_inner_differential_uniform 1 le_rfl 1 1 1 le_rfl one_pos le_rfl

end PhyslibExtTest.StatisticalMechanics.RandomCluster.TriHex.HexagonalOSSSUniform
