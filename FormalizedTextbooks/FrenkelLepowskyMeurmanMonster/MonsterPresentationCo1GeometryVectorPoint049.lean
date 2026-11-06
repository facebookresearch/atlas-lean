/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual two-core conjugation transport with complete checked binary action. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryBinaryMaskOperators
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryTransportLineProducts
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint001
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint017

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The literal actual two-core word for source point 49. -/
def monsterCo1GeometryVectorPoint49Transport : Co1 :=
  monsterCo1GeometryVectorPoint1Transport * monsterCo1GeometryTransportOperator 2 *
    monsterCo1GeometryVectorPoint1Transport⁻¹ * monsterCo1GeometryVectorPoint17Transport

/-- Complete displayed binary matrix of actual transport 49. -/
def monsterCo1GeometryVectorPoint49Matrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  ![![0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0],
    ![1, 1, 1, 0, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 0, 1, 0],
    ![0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 0, 0, 1, 0],
    ![0, 0, 0, 1, 0, 1, 1, 1, 0, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 1, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 1, 0, 1, 0],
    ![1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 1],
    ![0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1],
    ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0],
    ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1],
    ![1, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1],
    ![1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 1, 0],
    ![1, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 1, 1, 0],
    ![1, 1, 1, 0, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1],
    ![1, 1, 1, 1, 0, 1, 0, 0, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0],
    ![1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0],
    ![1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0],
    ![0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

/-- First complete finite matrix product in literal actual transport 49. -/
def monsterCo1GeometryVectorPoint49AfterSignMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
    ![0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]]

/-- Second complete finite matrix product in literal actual transport 49. -/
def monsterCo1GeometryVectorPoint49AfterInverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
    ![1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]]

set_option maxHeartbeats 24000000 in
-- Check every entry of this finite actual transport matrix in the Lean kernel.
/-- Every column of transport 49 is its actual Conway binary action. -/
theorem monsterCo1GeometryVectorPoint49Transport_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint49Transport v =
      monsterCo1GeometryVectorPoint49Matrix *ᵥ v := by
  have hx : monsterCo1GeometryVectorPoint1Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![57344, 53248, 45056, 28672, 16, 32, 64, 128, 256, 512, 8388608, 4194304, 4110, 8205,
    16395, 32775, 65536, 131072, 262144, 524288, 1048576, 2097152, 4196352, 8389632] := by
    decide +kernel
  have hxi : monsterCo1GeometryVectorPoint1InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![57345, 53250, 45060, 28680, 16, 32, 64, 128, 256, 512, 8389632, 4196352, 14, 13, 11, 7,
    65536, 131072, 262144, 524288, 1048576, 2097152, 2048, 1024] := by decide +kernel
  have hy : monsterCo1GeometryVectorPoint17Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![327820, 5167719, 5168842, 1041128, 37600, 8438480, 8438384, 21088, 28976, 45840, 8389632,
    13760653, 992421, 12848142, 12855971, 337569, 2107019, 15985327, 14871215, 3155591,
    10794911, 11826623, 1173645, 9888] := by decide +kernel
  have he : monsterCo1GeometryVectorPoint49AfterSignMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![57344, 8442880, 45056, 28672, 16, 32, 64, 128, 256, 512, 8388608, 4194317, 5134, 8205,
    17419, 33799, 66208, 131408, 262816, 524624, 1048736, 2097232, 4204544, 8389632] := by
    decide +kernel
  have hf : monsterCo1GeometryVectorPoint49AfterInverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![1, 8388610, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 10253, 8393728, 8192, 8406016,
    8422400, 66208, 131408, 262816, 524624, 1048736, 2097232, 4194317, 8388608] := by
      decide +kernel
  have hc : monsterCo1GeometryVectorPoint49Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![327820, 5176519, 5168842, 1041128, 37600, 8438480, 8438384, 21088, 28976, 45840, 8389632,
    5359661, 9373189, 12848142, 4458499, 8717313, 10487083, 7588623, 6473999, 11536167,
    2369327, 3417391, 5624867, 9888] := by decide +kernel
  have hc1 : monsterCo1GeometryVectorPoint1Matrix * monsterCo1GeometryTransportOperatorMatrix
    2 = monsterCo1GeometryVectorPoint49AfterSignMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![57344, 53248, 45056, 28672, 16, 32, 64, 128, 256, 512, 8388608, 4194304, 4110, 8205,
    16395, 32775, 65536, 131072, 262144, 524288, 1048576, 2097152, 4196352, 8389632]
      (monsterCo1GeometryBinaryOperatorMasks 2)
    ![57344, 8442880, 45056, 28672, 16, 32, 64, 128, 256, 512, 8388608, 4194317, 5134, 8205,
    17419, 33799, 66208, 131408, 262816, 524624, 1048736, 2097232, 4204544, 8389632] hx
    (monsterCo1GeometryBinaryOperatorMasks_decode 2) he (by decide +kernel)
  have hc2 : monsterCo1GeometryVectorPoint49AfterSignMatrix *
    monsterCo1GeometryVectorPoint1InverseMatrix =
    monsterCo1GeometryVectorPoint49AfterInverseMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![57344, 8442880, 45056, 28672, 16, 32, 64, 128, 256, 512, 8388608, 4194317, 5134, 8205,
    17419, 33799, 66208, 131408, 262816, 524624, 1048736, 2097232, 4204544, 8389632]
    ![57345, 53250, 45060, 28680, 16, 32, 64, 128, 256, 512, 8389632, 4196352, 14, 13, 11, 7,
    65536, 131072, 262144, 524288, 1048576, 2097152, 2048, 1024]
    ![1, 8388610, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 10253, 8393728, 8192, 8406016,
    8422400, 66208, 131408, 262816, 524624, 1048736, 2097232, 4194317, 8388608] he hxi hf (by
    decide +kernel)
  have hc3 : monsterCo1GeometryVectorPoint49AfterInverseMatrix *
    monsterCo1GeometryVectorPoint17Matrix = monsterCo1GeometryVectorPoint49Matrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![1, 8388610, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 10253, 8393728, 8192, 8406016,
    8422400, 66208, 131408, 262816, 524624, 1048736, 2097232, 4194317, 8388608]
    ![327820, 5167719, 5168842, 1041128, 37600, 8438480, 8438384, 21088, 28976, 45840, 8389632,
    13760653, 992421, 12848142, 12855971, 337569, 2107019, 15985327, 14871215, 3155591,
    10794911, 11826623, 1173645, 9888]
    ![327820, 5176519, 5168842, 1041128, 37600, 8438480, 8438384, 21088, 28976, 45840, 8389632,
    5359661, 9373189, 12848142, 4458499, 8717313, 10487083, 7588623, 6473999, 11536167,
    2369327, 3417391, 5624867, 9888] hf hy hc (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_line_products
    monsterCo1GeometryVectorPoint1Transport monsterCo1GeometryVectorPoint17Transport 2
    monsterCo1GeometryVectorPoint1Matrix monsterCo1GeometryVectorPoint1InverseMatrix
    monsterCo1GeometryVectorPoint17Matrix
    monsterCo1GeometryVectorPoint49AfterSignMatrix
    monsterCo1GeometryVectorPoint49AfterInverseMatrix monsterCo1GeometryVectorPoint49Matrix
    monsterCo1GeometryVectorPoint1Transport_binary
    monsterCo1GeometryVectorPoint1Transport_inverse_binary
    monsterCo1GeometryVectorPoint17Transport_binary
    hc1 hc2 hc3 v

/-- Source point 49 is the literal actual transported frame point. -/
def monsterCo1GeometryVectorPoint49 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryVectorPoint49Transport • monsterCo1GeometryBasePoint

/-- Complete binary coordinates of this literal actual source point. -/
theorem monsterCo1GeometryVectorPoint49_binary :
    monsterCo1GeometryVectorPoint49.val =
      ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0] := by
  change co1BinaryAction monsterCo1GeometryVectorPoint49Transport monsterCo1GeometryBasePoint.val =
      _
  rw [monsterCo1GeometryVectorPoint49Transport_binary, monsterCo1GeometryBasePoint_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
