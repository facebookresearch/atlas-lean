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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint090
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint100

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The literal actual two-core word for source point 145. -/
def monsterCo1GeometryVectorPoint145Transport : Co1 :=
  monsterCo1GeometryVectorPoint90Transport * monsterCo1GeometryTransportOperator 6 *
    monsterCo1GeometryVectorPoint90Transport⁻¹ * monsterCo1GeometryVectorPoint100Transport

/-- Complete displayed binary matrix of actual transport 145. -/
def monsterCo1GeometryVectorPoint145Matrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![10973582, 8902163, 8900997, 2584718, 8860658, 8414096, 10950190, 10950367, 505621,
      504243, 2618031, 2684560, 8716236, 6012167, 15082115, 7701380, 8679870, 4755902,
      13766063, 2555952, 4322733, 7871495, 291072, 1200]

/-- First complete finite matrix product in literal actual transport 145. -/
def monsterCo1GeometryVectorPoint145AfterSignMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![8438240, 8422912, 8430592, 1456, 8451136, 8450048, 8443280, 12640, 8418896, 8426192,
      8405408, 12911369, 5045249, 14138478, 16054728, 15005966, 4324356, 5922416, 1179840,
      8313787, 9540117, 6688667, 5560436, 8389632]

/-- Second complete finite matrix product in literal actual transport 145. -/
def monsterCo1GeometryVectorPoint145AfterInverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![8390103, 781, 1999, 1719, 16, 32, 1156, 8389974, 527, 8390306, 8389337, 6823528, 5305870,
      3723805, 1898475, 13657447, 4822178, 10651420, 13128332, 6607188, 553644, 15787367,
      11326013, 8388608]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 24000000 in
-- Check every entry of this finite actual transport matrix in the Lean kernel.
/-- Every column of transport 145 is its actual Conway binary action. -/
theorem monsterCo1GeometryVectorPoint145Transport_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint145Transport v =
      monsterCo1GeometryVectorPoint145Matrix *ᵥ v := by
  have hx : monsterCo1GeometryVectorPoint90Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![49312, 34000, 8431488, 8390064, 8451136, 8450048, 54464, 8400928, 29824, 8425488,
    8405552, 12910604, 5176840, 14007346, 16185927, 15137351, 4455428, 14179381, 1179654,
    8181864, 9539612, 6556882, 5692135, 8389632] := by rfl
  have hxi : monsterCo1GeometryVectorPoint90InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![4130239, 1785887, 5706941, 2586015, 8388882, 1117, 8390287, 161, 1510, 652, 8390335,
    15452462, 1068, 1614, 8390012, 8388993, 6333218, 4756642, 337548, 1373696, 49152, 4211725,
    1436211, 1727] := by rfl
  have hy : monsterCo1GeometryVectorPoint100Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![1041, 513571, 11006574, 2585529, 8860658, 8414096, 472565, 25408, 8894245, 8447216,
    34560, 14099015, 938853, 9364885, 5790597, 5790085, 13708597, 4549757, 4304552, 1670447,
    10356111, 5621254, 10320567, 1200] := by rfl
  have he : monsterCo1GeometryVectorPoint145AfterSignMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![8438240, 8422912, 8430592, 1456, 8451136, 8450048, 8443280, 12640, 8418896, 8426192,
    8405408, 12911369, 5045249, 14138478, 16054728, 15005966, 4324356, 5922416, 1179840,
    8313787, 9540117, 6688667, 5560436, 8389632] := by rfl
  have hf : monsterCo1GeometryVectorPoint145AfterInverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![8390103, 781, 1999, 1719, 16, 32, 1156, 8389974, 527, 8390306, 8389337, 6823528, 5305870,
    3723805, 1898475, 13657447, 4822178, 10651420, 13128332, 6607188, 553644, 15787367,
    11326013, 8388608] := by rfl
  have hc : monsterCo1GeometryVectorPoint145Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![10973582, 8902163, 8900997, 2584718, 8860658, 8414096, 10950190, 10950367, 505621,
    504243, 2618031, 2684560, 8716236, 6012167, 15082115, 7701380, 8679870, 4755902, 13766063,
    2555952, 4322733, 7871495, 291072, 1200] := by rfl
  have hc1 : monsterCo1GeometryVectorPoint90Matrix *
    monsterCo1GeometryTransportOperatorMatrix 6 =
    monsterCo1GeometryVectorPoint145AfterSignMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![49312, 34000, 8431488, 8390064, 8451136, 8450048, 54464, 8400928, 29824, 8425488,
    8405552, 12910604, 5176840, 14007346, 16185927, 15137351, 4455428, 14179381, 1179654,
    8181864, 9539612, 6556882, 5692135, 8389632]
      (monsterCo1GeometryBinaryOperatorMasks 6)
    ![8438240, 8422912, 8430592, 1456, 8451136, 8450048, 8443280, 12640, 8418896, 8426192,
    8405408, 12911369, 5045249, 14138478, 16054728, 15005966, 4324356, 5922416, 1179840,
    8313787, 9540117, 6688667, 5560436, 8389632] hx
    (monsterCo1GeometryBinaryOperatorMasks_decode 6) he (by decide +kernel)
  have hc2 : monsterCo1GeometryVectorPoint145AfterSignMatrix *
    monsterCo1GeometryVectorPoint90InverseMatrix =
    monsterCo1GeometryVectorPoint145AfterInverseMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![8438240, 8422912, 8430592, 1456, 8451136, 8450048, 8443280, 12640, 8418896, 8426192,
    8405408, 12911369, 5045249, 14138478, 16054728, 15005966, 4324356, 5922416, 1179840,
    8313787, 9540117, 6688667, 5560436, 8389632]
    ![4130239, 1785887, 5706941, 2586015, 8388882, 1117, 8390287, 161, 1510, 652, 8390335,
    15452462, 1068, 1614, 8390012, 8388993, 6333218, 4756642, 337548, 1373696, 49152, 4211725,
    1436211, 1727]
    ![8390103, 781, 1999, 1719, 16, 32, 1156, 8389974, 527, 8390306, 8389337, 6823528, 5305870,
    3723805, 1898475, 13657447, 4822178, 10651420, 13128332, 6607188, 553644, 15787367,
    11326013, 8388608] he hxi hf (by decide +kernel)
  have hc3 : monsterCo1GeometryVectorPoint145AfterInverseMatrix *
    monsterCo1GeometryVectorPoint100Matrix = monsterCo1GeometryVectorPoint145Matrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![8390103, 781, 1999, 1719, 16, 32, 1156, 8389974, 527, 8390306, 8389337, 6823528, 5305870,
    3723805, 1898475, 13657447, 4822178, 10651420, 13128332, 6607188, 553644, 15787367,
    11326013, 8388608]
    ![1041, 513571, 11006574, 2585529, 8860658, 8414096, 472565, 25408, 8894245, 8447216,
    34560, 14099015, 938853, 9364885, 5790597, 5790085, 13708597, 4549757, 4304552, 1670447,
    10356111, 5621254, 10320567, 1200]
    ![10973582, 8902163, 8900997, 2584718, 8860658, 8414096, 10950190, 10950367, 505621,
    504243, 2618031, 2684560, 8716236, 6012167, 15082115, 7701380, 8679870, 4755902, 13766063,
    2555952, 4322733, 7871495, 291072, 1200] hf hy hc (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_line_products
    monsterCo1GeometryVectorPoint90Transport monsterCo1GeometryVectorPoint100Transport 6
    monsterCo1GeometryVectorPoint90Matrix monsterCo1GeometryVectorPoint90InverseMatrix
    monsterCo1GeometryVectorPoint100Matrix
    monsterCo1GeometryVectorPoint145AfterSignMatrix
    monsterCo1GeometryVectorPoint145AfterInverseMatrix monsterCo1GeometryVectorPoint145Matrix
    monsterCo1GeometryVectorPoint90Transport_binary
    monsterCo1GeometryVectorPoint90Transport_inverse_binary
    monsterCo1GeometryVectorPoint100Transport_binary
    hc1 hc2 hc3 v

/-- Source point 145 is the literal actual transported frame point. -/
def monsterCo1GeometryVectorPoint145 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryVectorPoint145Transport • monsterCo1GeometryBasePoint

/-- Complete binary coordinates of this literal actual source point. -/
theorem monsterCo1GeometryVectorPoint145_binary :
    monsterCo1GeometryVectorPoint145.val =
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0] := by
  change co1BinaryAction monsterCo1GeometryVectorPoint145Transport monsterCo1GeometryBasePoint.val =
      _
  rw [monsterCo1GeometryVectorPoint145Transport_binary, monsterCo1GeometryBasePoint_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
