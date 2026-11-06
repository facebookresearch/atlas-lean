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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint016

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The literal actual two-core word for source point 48. -/
def monsterCo1GeometryVectorPoint48Transport : Co1 :=
  monsterCo1GeometryVectorPoint12Transport * monsterCo1GeometryTransportOperator 1 *
    monsterCo1GeometryVectorPoint12Transport⁻¹ * monsterCo1GeometryVectorPoint16Transport

/-- Complete displayed binary matrix of actual transport 48. -/
def monsterCo1GeometryVectorPoint48Matrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 1, 1, 0, 0, 1, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1],
    ![1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1],
    ![1, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0],
    ![1, 0, 0, 0, 1, 0, 1, 1, 0, 1, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 1],
    ![1, 0, 0, 0, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 1],
    ![1, 1, 1, 1, 0, 1, 1, 0, 0, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0],
    ![0, 1, 1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0],
    ![0, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 1, 0],
    ![0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1],
    ![1, 0, 1, 1, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 0, 0, 1, 1],
    ![0, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0, 1, 1, 1, 1, 1, 0, 1, 1],
    ![0, 1, 1, 1, 0, 0, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1],
    ![1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1],
    ![1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0],
    ![1, 1, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
    ![1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1],
    ![1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 1, 0, 0, 0, 1, 1, 1],
    ![1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0],
    ![0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0],
    ![0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]]

/-- First complete finite matrix product in literal actual transport 48. -/
def monsterCo1GeometryVectorPoint48AfterSignMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
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

/-- Second complete finite matrix product in literal actual transport 48. -/
def monsterCo1GeometryVectorPoint48AfterInverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
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
/-- Every column of transport 48 is its actual Conway binary action. -/
theorem monsterCo1GeometryVectorPoint48Transport_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint48Transport v =
      monsterCo1GeometryVectorPoint48Matrix *ᵥ v := by
  have hx : monsterCo1GeometryVectorPoint12Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![128, 8450752, 8442048, 57568, 37600, 8438480, 8438384, 21088, 28976, 45840, 8397472,
    12587008, 1041989, 4471982, 4470787, 328737, 2107019, 15985327, 14871215, 3155591,
    10794911, 11826623, 13760653, 8389632] := by decide +kernel
  have hxi : monsterCo1GeometryVectorPoint12InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![12150534, 7383031, 2025057, 2614625, 1065, 97, 783, 1, 1696, 1008, 8389734, 13004640,
    2045, 1014, 2019, 1906, 3539712, 6128234, 1040385, 4454386, 3146496, 7283185, 2971, 1126]
    := by decide +kernel
  have hy : monsterCo1GeometryVectorPoint16Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![128, 13691598, 12593359, 58593, 5270255, 9488081, 9487985, 5286511, 6327614, 7360286,
    9488032, 9815203, 6231749, 8712320, 323724, 8716416, 8388906, 209664, 143616, 8389414,
    10778801, 11843729, 13706275, 58368] := by decide +kernel
  have he : monsterCo1GeometryVectorPoint48AfterSignMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![128, 63168, 8442048, 8447200, 8427232, 8438480, 8438384, 8410720, 28976, 45840, 9888,
    12587022, 1041013, 12855470, 4467715, 8717313, 2106251, 15990175, 14876607, 3154311,
    2406047, 3438271, 13758125, 8389632] := by decide +kernel
  have hf : monsterCo1GeometryVectorPoint48AfterInverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![1, 8388610, 4, 8388616, 8388624, 32, 64, 8388736, 256, 512, 8389632, 4828407, 8392750,
    8398845, 8405915, 33799, 8454854, 8520323, 8651026, 8913206, 1049286, 2097462, 12582922,
    8388608] := by decide +kernel
  have hc : monsterCo1GeometryVectorPoint48Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![128, 13635278, 12593359, 225, 5279471, 9488081, 9487985, 5262959, 6327614, 7360286,
    9446048, 12965517, 14619380, 12852366, 12851331, 328865, 2098219, 15980607, 14866463,
    3146791, 301488, 285584, 118284, 58368] := by decide +kernel
  have hc1 : monsterCo1GeometryVectorPoint12Matrix *
    monsterCo1GeometryTransportOperatorMatrix 1 =
    monsterCo1GeometryVectorPoint48AfterSignMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![128, 8450752, 8442048, 57568, 37600, 8438480, 8438384, 21088, 28976, 45840, 8397472,
    12587008, 1041989, 4471982, 4470787, 328737, 2107019, 15985327, 14871215, 3155591,
    10794911, 11826623, 13760653, 8389632]
      (monsterCo1GeometryBinaryOperatorMasks 1)
    ![128, 63168, 8442048, 8447200, 8427232, 8438480, 8438384, 8410720, 28976, 45840, 9888,
    12587022, 1041013, 12855470, 4467715, 8717313, 2106251, 15990175, 14876607, 3154311,
    2406047, 3438271, 13758125, 8389632] hx (monsterCo1GeometryBinaryOperatorMasks_decode 1) he
    (by decide +kernel)
  have hc2 : monsterCo1GeometryVectorPoint48AfterSignMatrix *
    monsterCo1GeometryVectorPoint12InverseMatrix =
    monsterCo1GeometryVectorPoint48AfterInverseMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![128, 63168, 8442048, 8447200, 8427232, 8438480, 8438384, 8410720, 28976, 45840, 9888,
    12587022, 1041013, 12855470, 4467715, 8717313, 2106251, 15990175, 14876607, 3154311,
    2406047, 3438271, 13758125, 8389632]
    ![12150534, 7383031, 2025057, 2614625, 1065, 97, 783, 1, 1696, 1008, 8389734, 13004640,
    2045, 1014, 2019, 1906, 3539712, 6128234, 1040385, 4454386, 3146496, 7283185, 2971, 1126]
    ![1, 8388610, 4, 8388616, 8388624, 32, 64, 8388736, 256, 512, 8389632, 4828407, 8392750,
    8398845, 8405915, 33799, 8454854, 8520323, 8651026, 8913206, 1049286, 2097462, 12582922,
    8388608] he hxi hf (by decide +kernel)
  have hc3 : monsterCo1GeometryVectorPoint48AfterInverseMatrix *
    monsterCo1GeometryVectorPoint16Matrix = monsterCo1GeometryVectorPoint48Matrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![1, 8388610, 4, 8388616, 8388624, 32, 64, 8388736, 256, 512, 8389632, 4828407, 8392750,
    8398845, 8405915, 33799, 8454854, 8520323, 8651026, 8913206, 1049286, 2097462, 12582922,
    8388608]
    ![128, 13691598, 12593359, 58593, 5270255, 9488081, 9487985, 5286511, 6327614, 7360286,
    9488032, 9815203, 6231749, 8712320, 323724, 8716416, 8388906, 209664, 143616, 8389414,
    10778801, 11843729, 13706275, 58368]
    ![128, 13635278, 12593359, 225, 5279471, 9488081, 9487985, 5262959, 6327614, 7360286,
    9446048, 12965517, 14619380, 12852366, 12851331, 328865, 2098219, 15980607, 14866463,
    3146791, 301488, 285584, 118284, 58368] hf hy hc (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_line_products
    monsterCo1GeometryVectorPoint12Transport monsterCo1GeometryVectorPoint16Transport 1
    monsterCo1GeometryVectorPoint12Matrix monsterCo1GeometryVectorPoint12InverseMatrix
    monsterCo1GeometryVectorPoint16Matrix
    monsterCo1GeometryVectorPoint48AfterSignMatrix
    monsterCo1GeometryVectorPoint48AfterInverseMatrix monsterCo1GeometryVectorPoint48Matrix
    monsterCo1GeometryVectorPoint12Transport_binary
    monsterCo1GeometryVectorPoint12Transport_inverse_binary
    monsterCo1GeometryVectorPoint16Transport_binary
    hc1 hc2 hc3 v

/-- Source point 48 is the literal actual transported frame point. -/
def monsterCo1GeometryVectorPoint48 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryVectorPoint48Transport • monsterCo1GeometryBasePoint

/-- Complete binary coordinates of this literal actual source point. -/
theorem monsterCo1GeometryVectorPoint48_binary :
    monsterCo1GeometryVectorPoint48.val =
      ![0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 1, 1, 0] := by
  change co1BinaryAction monsterCo1GeometryVectorPoint48Transport monsterCo1GeometryBasePoint.val =
      _
  rw [monsterCo1GeometryVectorPoint48Transport_binary, monsterCo1GeometryBasePoint_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
