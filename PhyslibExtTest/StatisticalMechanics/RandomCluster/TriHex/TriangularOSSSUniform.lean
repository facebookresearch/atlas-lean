/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.TriHex.TriangularOSSSUniform

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.TriHex.TriangularOSSSUniform`

* `triangularSharpConstant 0 = 1 / 8` (from `e^{-6β₀} / 8`), and it is positive;
* `triangularBox_root_degree_le_six` in the box of radius `1`;
* `triangularOuterCenteredConn_zero`: connection to the radius-`0` centered shell is certain;
* `triangular_outer_inner_differential_uniform` at `n = 1`, `q = 1`, `β = β₀ = 1`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.TriHex.TriangularOSSSUniform

open _root_.StatMech.FK.PeriodicPlanar

-- The uniform OSSS constant at `β₀ = 0`.
example : triangularSharpConstant 0 = 1 / 8 := by
  simp [triangularSharpConstant]

example : 0 < triangularSharpConstant 1 :=
  triangularSharpConstant_pos 1

-- The origin has at most six neighbours in the box of radius `1`.
example : (triangularBoxGraph 1).degree (triangularBoxRoot 1) ≤ 6 :=
  triangularBox_root_degree_le_six 1 le_rfl

-- Connection to the centered shell of radius `0` has probability one.
example (x : TriangularBoxVertex 2) : triangularOuterCenteredConn 2 1 1 x 0 = 1 :=
  triangularOuterCenteredConn_zero 2 1 1 le_rfl one_pos x

-- The uniform differential inequality at a concrete parameter point.
example : triangularSharpConstant 1 *
      (((1 : ℕ) / triangularOuterInnerSig 1 1 1) * triangularOuterInnerTheta 1 1 1) ≤
    triangularOuterInnerThetaPrime 1 1 1 :=
  triangular_outer_inner_differential_uniform 1 le_rfl 1 1 1 le_rfl one_pos le_rfl

end PhyslibExtTest.StatisticalMechanics.RandomCluster.TriHex.TriangularOSSSUniform
