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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint006
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint057

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The literal actual two-core word for source point 101. -/
def monsterCo1GeometryVectorPoint101Transport : Co1 :=
  monsterCo1GeometryVectorPoint6Transport * monsterCo1GeometryTransportOperator 6 *
    monsterCo1GeometryVectorPoint6Transport⁻¹ * monsterCo1GeometryVectorPoint57Transport

/-- Complete displayed binary matrix of actual transport 101. -/
def monsterCo1GeometryVectorPoint101Matrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![10974526, 8902163, 2617657, 2619230, 10983048, 2147580, 58432, 505091, 10503547,
      10949231, 8868211, 7799467, 1361300, 7107841, 14765428, 7531587, 267950, 8123139,
      13759254, 5359413, 4546086, 3837452, 2386792, 1200]

/-- First complete finite matrix product in literal actual transport 101. -/
def monsterCo1GeometryVectorPoint101AfterSignMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![8438240, 33280, 33024, 33536, 46032, 21424, 29200, 8426192, 53712, 12640, 57872, 4203504,
      9307648, 1377231, 15199579, 16248221, 12651524, 13241606, 12585991, 13504000, 12782594,
      12979974, 4655367, 8389632]

/-- Second complete finite matrix product in literal actual transport 101. -/
def monsterCo1GeometryVectorPoint101AfterInverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![376, 1218, 1220, 1224, 597, 1915, 1152, 1698, 1383, 889, 1762, 2971, 11730956, 14296612,
      1131627, 10654277, 10686464, 7999494, 7598092, 13426688, 11669504, 15400970, 6217734,
      8388608]

set_option maxHeartbeats 24000000 in
-- Check every entry of this finite actual transport matrix in the Lean kernel.
/-- Every column of transport 101 is its actual Conway binary action. -/
theorem monsterCo1GeometryVectorPoint101Transport_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint101Transport v =
      monsterCo1GeometryVectorPoint101Matrix *ᵥ v := by
  have hx : monsterCo1GeometryVectorPoint6Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![49312, 8421584, 8422352, 8421840, 8433728, 8409136, 8417472, 8425488, 8441984, 8400928,
    8446464, 4203168, 9307142, 1376268, 6680077, 7728653, 12782596, 13110277, 12717064,
    13372425, 12651522, 12848131, 4524557, 8389632] := by decide +kernel
  have hxi : monsterCo1GeometryVectorPoint6InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![4128768, 15007756, 5640204, 5894156, 1310, 81, 1679, 161, 10, 12, 8390652, 8383473, 1708,
    769, 1087, 1230, 712704, 10620928, 385024, 9760768, 49152, 12600332, 3069, 2044] := by
      decide +kernel
  have hy : monsterCo1GeometryVectorPoint57Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![1041, 513571, 11006217, 11007854, 8447136, 58400, 8447088, 8447216, 26272, 25408,
    8388784, 14099015, 14160, 1552, 8256, 8768, 5352069, 12938698, 13584682, 6000589, 1106445,
    9495041, 12910962, 1200] := by decide +kernel
  have he : monsterCo1GeometryVectorPoint101AfterSignMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![8438240, 33280, 33024, 33536, 46032, 21424, 29200, 8426192, 53712, 12640, 57872, 4203504,
    9307648, 1377231, 15199579, 16248221, 12651524, 13241606, 12585991, 13504000, 12782594,
    12979974, 4655367, 8389632] := by rfl
  have hf : monsterCo1GeometryVectorPoint101AfterInverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![376, 1218, 1220, 1224, 597, 1915, 1152, 1698, 1383, 889, 1762, 2971, 11730956, 14296612,
    1131627, 10654277, 10686464, 7999494, 7598092, 13426688, 11669504, 15400970, 6217734,
    8388608] := by rfl
  have hc : monsterCo1GeometryVectorPoint101Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![10974526, 8902163, 2617657, 2619230, 10983048, 2147580, 58432, 505091, 10503547,
    10949231, 8868211, 7799467, 1361300, 7107841, 14765428, 7531587, 267950, 8123139, 13759254,
    5359413, 4546086, 3837452, 2386792, 1200] := by rfl
  have hc1 : monsterCo1GeometryVectorPoint6Matrix * monsterCo1GeometryTransportOperatorMatrix
    6 = monsterCo1GeometryVectorPoint101AfterSignMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![49312, 8421584, 8422352, 8421840, 8433728, 8409136, 8417472, 8425488, 8441984, 8400928,
    8446464, 4203168, 9307142, 1376268, 6680077, 7728653, 12782596, 13110277, 12717064,
    13372425, 12651522, 12848131, 4524557, 8389632]
      (monsterCo1GeometryBinaryOperatorMasks 6)
    ![8438240, 33280, 33024, 33536, 46032, 21424, 29200, 8426192, 53712, 12640, 57872, 4203504,
    9307648, 1377231, 15199579, 16248221, 12651524, 13241606, 12585991, 13504000, 12782594,
    12979974, 4655367, 8389632] hx (monsterCo1GeometryBinaryOperatorMasks_decode 6) he (by
    decide +kernel)
  have hc2 : monsterCo1GeometryVectorPoint101AfterSignMatrix *
    monsterCo1GeometryVectorPoint6InverseMatrix =
    monsterCo1GeometryVectorPoint101AfterInverseMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![8438240, 33280, 33024, 33536, 46032, 21424, 29200, 8426192, 53712, 12640, 57872, 4203504,
    9307648, 1377231, 15199579, 16248221, 12651524, 13241606, 12585991, 13504000, 12782594,
    12979974, 4655367, 8389632]
    ![4128768, 15007756, 5640204, 5894156, 1310, 81, 1679, 161, 10, 12, 8390652, 8383473, 1708,
    769, 1087, 1230, 712704, 10620928, 385024, 9760768, 49152, 12600332, 3069, 2044]
    ![376, 1218, 1220, 1224, 597, 1915, 1152, 1698, 1383, 889, 1762, 2971, 11730956, 14296612,
    1131627, 10654277, 10686464, 7999494, 7598092, 13426688, 11669504, 15400970, 6217734,
    8388608] he hxi hf (by decide +kernel)
  have hc3 : monsterCo1GeometryVectorPoint101AfterInverseMatrix *
    monsterCo1GeometryVectorPoint57Matrix = monsterCo1GeometryVectorPoint101Matrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![376, 1218, 1220, 1224, 597, 1915, 1152, 1698, 1383, 889, 1762, 2971, 11730956, 14296612,
    1131627, 10654277, 10686464, 7999494, 7598092, 13426688, 11669504, 15400970, 6217734,
    8388608]
    ![1041, 513571, 11006217, 11007854, 8447136, 58400, 8447088, 8447216, 26272, 25408,
    8388784, 14099015, 14160, 1552, 8256, 8768, 5352069, 12938698, 13584682, 6000589, 1106445,
    9495041, 12910962, 1200]
    ![10974526, 8902163, 2617657, 2619230, 10983048, 2147580, 58432, 505091, 10503547,
    10949231, 8868211, 7799467, 1361300, 7107841, 14765428, 7531587, 267950, 8123139, 13759254,
    5359413, 4546086, 3837452, 2386792, 1200] hf hy hc (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_line_products
    monsterCo1GeometryVectorPoint6Transport monsterCo1GeometryVectorPoint57Transport 6
    monsterCo1GeometryVectorPoint6Matrix monsterCo1GeometryVectorPoint6InverseMatrix
    monsterCo1GeometryVectorPoint57Matrix
    monsterCo1GeometryVectorPoint101AfterSignMatrix
    monsterCo1GeometryVectorPoint101AfterInverseMatrix monsterCo1GeometryVectorPoint101Matrix
    monsterCo1GeometryVectorPoint6Transport_binary
    monsterCo1GeometryVectorPoint6Transport_inverse_binary
    monsterCo1GeometryVectorPoint57Transport_binary
    hc1 hc2 hc3 v

/-- Source point 101 is the literal actual transported frame point. -/
def monsterCo1GeometryVectorPoint101 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryVectorPoint101Transport • monsterCo1GeometryBasePoint

/-- Complete binary coordinates of this literal actual source point. -/
theorem monsterCo1GeometryVectorPoint101_binary :
    monsterCo1GeometryVectorPoint101.val =
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 0] := by
  change co1BinaryAction monsterCo1GeometryVectorPoint101Transport monsterCo1GeometryBasePoint.val =
      _
  rw [monsterCo1GeometryVectorPoint101Transport_binary, monsterCo1GeometryBasePoint_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
