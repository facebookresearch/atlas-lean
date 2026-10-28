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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint012
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint017

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The literal actual two-core word for source point 51. -/
def monsterCo1GeometryVectorPoint51Transport : Co1 :=
  monsterCo1GeometryVectorPoint12Transport * monsterCo1GeometryTransportOperator 1 *
    monsterCo1GeometryVectorPoint12Transport⁻¹ * monsterCo1GeometryVectorPoint17Transport

/-- Complete displayed binary matrix of actual transport 51. -/
def monsterCo1GeometryVectorPoint51Matrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  ![![0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0],
    ![1, 1, 1, 0, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 0, 1, 0],
    ![0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 0, 0, 1, 0],
    ![0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 1, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 0, 0, 1, 0, 1, 0, 0, 1],
    ![0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1],
    ![0, 0, 1, 0, 1, 0, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 0, 1],
    ![0, 0, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 1, 0, 1],
    ![0, 1, 0, 1, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1],
    ![0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0],
    ![0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 1, 0, 0],
    ![0, 1, 0, 0, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 0, 1, 0],
    ![0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

/-- First complete finite matrix product in literal actual transport 51. -/
def monsterCo1GeometryVectorPoint51AfterSignMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1],
    ![1, 0, 1, 0, 1, 1, 1, 0, 0, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0],
    ![0, 1, 1, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1],
    ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0],
    ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1],
    ![1, 1, 0, 1, 0, 0, 0, 1, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
    ![1, 1, 1, 1, 1, 0, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1],
    ![1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 0, 1, 1, 1],
    ![1, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0],
    ![1, 1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0],
    ![1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 0, 0, 1, 0, 1, 1, 0, 0],
    ![1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]]

/-- Second complete finite matrix product in literal actual transport 51. -/
def monsterCo1GeometryVectorPoint51AfterInverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![1, 1, 1, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0, 1, 0, 0, 1, 0],
    ![0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![1, 1, 0, 1, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 1, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1],
    ![1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1],
    ![0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1],
    ![0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1],
    ![0, 1, 1, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
    ![0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
    ![0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]]

set_option maxHeartbeats 24000000 in
-- Check every entry of this finite actual transport matrix in the Lean kernel.
/-- Every column of transport 51 is its actual Conway binary action. -/
theorem monsterCo1GeometryVectorPoint51Transport_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint51Transport v =
      monsterCo1GeometryVectorPoint51Matrix *ᵥ v := by
  have hx : monsterCo1GeometryVectorPoint12Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![128, 8450752, 8442048, 57568, 37600, 8438480, 8438384, 21088, 28976, 45840, 8397472,
    12587008, 1041989, 4471982, 4470787, 328737, 2107019, 15985327, 14871215, 3155591,
    10794911, 11826623, 13760653, 8389632] := by decide +kernel
  have hxi : monsterCo1GeometryVectorPoint12InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![12150534, 7383031, 2025057, 2614625, 1065, 97, 783, 1, 1696, 1008, 8389734, 13004640,
    2045, 1014, 2019, 1906, 3539712, 6128234, 1040385, 4454386, 3146496, 7283185, 2971, 1126]
    := by decide +kernel
  have hy : monsterCo1GeometryVectorPoint17Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![327820, 5167719, 5168842, 1041128, 37600, 8438480, 8438384, 21088, 28976, 45840, 8389632,
    13760653, 992421, 12848142, 12855971, 337569, 2107019, 15985327, 14871215, 3155591,
    10794911, 11826623, 1173645, 9888] := by decide +kernel
  have he : monsterCo1GeometryVectorPoint51AfterSignMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![128, 63168, 8442048, 8447200, 8427232, 8438480, 8438384, 8410720, 28976, 45840, 9888,
    12587022, 1041013, 12855470, 4467715, 8717313, 2106251, 15990175, 14876607, 3154311,
    2406047, 3438271, 13758125, 8389632] := by decide +kernel
  have hf : monsterCo1GeometryVectorPoint51AfterInverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![1, 8388610, 4, 8388616, 8388624, 32, 64, 8388736, 256, 512, 8389632, 4828407, 8392750,
    8398845, 8405915, 33799, 8454854, 8520323, 8651026, 8913206, 1049286, 2097462, 12582922,
    8388608] := by decide +kernel
  have hc : monsterCo1GeometryVectorPoint51Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![327820, 5176519, 5168842, 1033288, 46144, 8438480, 8438384, 29888, 28976, 45840, 8397472,
    9763490, 8398480, 4096, 8402592, 8398464, 10495878, 12122004, 11335096, 11543946, 2396210,
    3428370, 5306018, 9888] := by decide +kernel
  have hc1 : monsterCo1GeometryVectorPoint12Matrix *
    monsterCo1GeometryTransportOperatorMatrix 1 =
    monsterCo1GeometryVectorPoint51AfterSignMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![128, 8450752, 8442048, 57568, 37600, 8438480, 8438384, 21088, 28976, 45840, 8397472,
    12587008, 1041989, 4471982, 4470787, 328737, 2107019, 15985327, 14871215, 3155591,
    10794911, 11826623, 13760653, 8389632]
      (monsterCo1GeometryBinaryOperatorMasks 1)
    ![128, 63168, 8442048, 8447200, 8427232, 8438480, 8438384, 8410720, 28976, 45840, 9888,
    12587022, 1041013, 12855470, 4467715, 8717313, 2106251, 15990175, 14876607, 3154311,
    2406047, 3438271, 13758125, 8389632] hx (monsterCo1GeometryBinaryOperatorMasks_decode 1) he
    (by decide +kernel)
  have hc2 : monsterCo1GeometryVectorPoint51AfterSignMatrix *
    monsterCo1GeometryVectorPoint12InverseMatrix =
    monsterCo1GeometryVectorPoint51AfterInverseMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![128, 63168, 8442048, 8447200, 8427232, 8438480, 8438384, 8410720, 28976, 45840, 9888,
    12587022, 1041013, 12855470, 4467715, 8717313, 2106251, 15990175, 14876607, 3154311,
    2406047, 3438271, 13758125, 8389632]
    ![12150534, 7383031, 2025057, 2614625, 1065, 97, 783, 1, 1696, 1008, 8389734, 13004640,
    2045, 1014, 2019, 1906, 3539712, 6128234, 1040385, 4454386, 3146496, 7283185, 2971, 1126]
    ![1, 8388610, 4, 8388616, 8388624, 32, 64, 8388736, 256, 512, 8389632, 4828407, 8392750,
    8398845, 8405915, 33799, 8454854, 8520323, 8651026, 8913206, 1049286, 2097462, 12582922,
    8388608] he hxi hf (by decide +kernel)
  have hc3 : monsterCo1GeometryVectorPoint51AfterInverseMatrix *
    monsterCo1GeometryVectorPoint17Matrix = monsterCo1GeometryVectorPoint51Matrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![1, 8388610, 4, 8388616, 8388624, 32, 64, 8388736, 256, 512, 8389632, 4828407, 8392750,
    8398845, 8405915, 33799, 8454854, 8520323, 8651026, 8913206, 1049286, 2097462, 12582922,
    8388608]
    ![327820, 5167719, 5168842, 1041128, 37600, 8438480, 8438384, 21088, 28976, 45840, 8389632,
    13760653, 992421, 12848142, 12855971, 337569, 2107019, 15985327, 14871215, 3155591,
    10794911, 11826623, 1173645, 9888]
    ![327820, 5176519, 5168842, 1033288, 46144, 8438480, 8438384, 29888, 28976, 45840, 8397472,
    9763490, 8398480, 4096, 8402592, 8398464, 10495878, 12122004, 11335096, 11543946, 2396210,
    3428370, 5306018, 9888] hf hy hc (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_line_products
    monsterCo1GeometryVectorPoint12Transport monsterCo1GeometryVectorPoint17Transport 1
    monsterCo1GeometryVectorPoint12Matrix monsterCo1GeometryVectorPoint12InverseMatrix
    monsterCo1GeometryVectorPoint17Matrix
    monsterCo1GeometryVectorPoint51AfterSignMatrix
    monsterCo1GeometryVectorPoint51AfterInverseMatrix monsterCo1GeometryVectorPoint51Matrix
    monsterCo1GeometryVectorPoint12Transport_binary
    monsterCo1GeometryVectorPoint12Transport_inverse_binary
    monsterCo1GeometryVectorPoint17Transport_binary
    hc1 hc2 hc3 v

/-- The displayed inverse matrix of actual source transport 51. -/
def monsterCo1GeometryVectorPoint51InverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  ![![0, 1, 1, 0, 0, 1, 1, 0, 1, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 0, 1],
    ![1, 0, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 0, 1, 1, 1, 1, 1],
    ![0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1, 0, 1, 1, 1, 1, 0, 0, 1],
    ![0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1, 0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0],
    ![0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0],
    ![1, 0, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 0, 0, 1, 0, 1, 0, 0, 1, 1],
    ![0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0],
    ![1, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1],
    ![1, 0, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 0, 1, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1]]

set_option maxHeartbeats 24000000 in
-- Check all entries of the right inverse before applying actual action injectivity.
/-- The inverse matrix is the inverse of the literal actual Conway transport. -/
theorem monsterCo1GeometryVectorPoint51Transport_inverse_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint51Transport⁻¹ v =
      monsterCo1GeometryVectorPoint51InverseMatrix *ᵥ v := by
  have hm : monsterCo1GeometryVectorPoint51Matrix = monsterCo1GeometryBinaryMaskMatrix
      ![327820, 5176519, 5168842, 1033288, 46144, 8438480, 8438384, 29888, 28976, 45840,
        8397472, 9763490, 8398480, 4096, 8402592, 8398464, 10495878, 12122004, 11335096,
        11543946, 2396210, 3428370, 5306018, 9888] := by decide +kernel
  have hmi : monsterCo1GeometryVectorPoint51InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
      ![12150630, 16329981, 10413664, 11003232, 36864, 57344, 8450880, 57440, 8390304, 1008,
        25600, 12976381, 8192, 8415120, 12336, 53440, 3539809, 13897028, 1040384, 13270269,
        3145968, 15092797, 650493, 8413184] := by decide +kernel
  have hi : (1 : Matrix (Fin 24) (Fin 24) (ZMod 2)) = monsterCo1GeometryBinaryMaskMatrix
      ![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536,
        131072, 262144, 524288, 1048576, 2097152, 4194304, 8388608] := by decide +kernel
  have hc : monsterCo1GeometryVectorPoint51Matrix *
    monsterCo1GeometryVectorPoint51InverseMatrix = 1 :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
      ![327820, 5176519, 5168842, 1033288, 46144, 8438480, 8438384, 29888, 28976, 45840,
        8397472, 9763490, 8398480, 4096, 8402592, 8398464, 10495878, 12122004, 11335096,
        11543946, 2396210, 3428370, 5306018, 9888]
      ![12150630, 16329981, 10413664, 11003232, 36864, 57344, 8450880, 57440, 8390304, 1008,
        25600, 12976381, 8192, 8415120, 12336, 53440, 3539809, 13897028, 1040384, 13270269,
        3145968, 15092797, 650493, 8413184]
      ![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536,
        131072, 262144, 524288, 1048576, 2097152, 4194304, 8388608] hm hmi hi
      (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_inv monsterCo1GeometryVectorPoint51Transport _ _
    monsterCo1GeometryVectorPoint51Transport_binary hc v

/-- Source point 51 is the literal actual transported frame point. -/
def monsterCo1GeometryVectorPoint51 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryVectorPoint51Transport • monsterCo1GeometryBasePoint

/-- Complete binary coordinates of this literal actual source point. -/
theorem monsterCo1GeometryVectorPoint51_binary :
    monsterCo1GeometryVectorPoint51.val =
      ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  change co1BinaryAction monsterCo1GeometryVectorPoint51Transport monsterCo1GeometryBasePoint.val =
      _
  rw [monsterCo1GeometryVectorPoint51Transport_binary, monsterCo1GeometryBasePoint_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
