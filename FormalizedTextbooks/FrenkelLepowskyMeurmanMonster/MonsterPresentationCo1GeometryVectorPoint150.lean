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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint040
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint127

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The literal actual two-core word for source point 150. -/
def monsterCo1GeometryVectorPoint150Transport : Co1 :=
  monsterCo1GeometryVectorPoint40Transport * monsterCo1GeometryTransportOperator 5 *
    monsterCo1GeometryVectorPoint40Transport⁻¹ * monsterCo1GeometryVectorPoint127Transport

/-- Complete displayed binary matrix of actual transport 150. -/
def monsterCo1GeometryVectorPoint150Matrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![13280, 8401904, 13248, 8430880, 8417408, 8417472, 8450624, 8405984, 8406272, 8451328,
      37968, 8478263, 15391043, 6319194, 13871476, 14790073, 8247719, 12974906, 9478477,
      15330736, 13712034, 1107574, 6397754, 8389632]

/-- First complete finite matrix product in literal actual transport 150. -/
def monsterCo1GeometryVectorPoint150AfterSignMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![49696, 8422320, 11567350, 10519162, 12692864, 12667345, 12676992, 12684145, 12701184,
      4270721, 9438860, 4511790, 10380303, 377344, 13968290, 13967778, 8647733, 529196,
      8582169, 790828, 4251309, 12966944, 5629058, 8447008]

/-- Second complete finite matrix product in literal actual transport 150. -/
def monsterCo1GeometryVectorPoint150AfterInverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![49312, 12616401, 15963990, 16545786, 6311375, 6311342, 6327614, 6327727, 10538589,
      2084364, 1041568, 1106957, 10037900, 1032352, 12534609, 12550993, 1371308, 5149778,
      1174700, 4961363, 1035276, 3206157, 16761840, 4129617]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 24000000 in
-- Check every entry of this finite actual transport matrix in the Lean kernel.
/-- Every column of transport 150 is its actual Conway binary action. -/
theorem monsterCo1GeometryVectorPoint150Transport_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint150Transport v =
      monsterCo1GeometryVectorPoint150Matrix *ᵥ v := by
  have hx : monsterCo1GeometryVectorPoint40Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![49312, 8421584, 11568080, 10518992, 12627023, 12601406, 12610767, 12617758, 12635279,
    12593198, 9438720, 12966029, 10380998, 377484, 5579650, 5579138, 259130, 8917002, 193558,
    9179142, 12704770, 4512899, 14018082, 58368] := by decide +kernel
  have hxi : monsterCo1GeometryVectorPoint40InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![8389616, 2427997, 9838419, 10092370, 8389918, 81, 8390287, 161, 4211725, 49152, 12519180,
    16770465, 9765376, 4130813, 12517571, 12517426, 712784, 2233360, 385025, 9761295, 49164,
    4211719, 5574481, 12518144] := by decide +kernel
  have hy : monsterCo1GeometryVectorPoint127Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![3291117, 12611, 1292073, 5150, 10713103, 10733935, 9567938, 9567810, 2358812, 10746248,
    9675143, 222053, 10754264, 15948173, 5447392, 6363693, 1219807, 5667175, 16770101,
    14376503, 15873578, 9624356, 13839523, 45972] := by rfl
  have he : monsterCo1GeometryVectorPoint150AfterSignMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![49696, 8422320, 11567350, 10519162, 12692864, 12667345, 12676992, 12684145, 12701184,
    4270721, 9438860, 4511790, 10380303, 377344, 13968290, 13967778, 8647733, 529196, 8582169,
    790828, 4251309, 12966944, 5629058, 8447008] := by rfl
  have hf : monsterCo1GeometryVectorPoint150AfterInverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![49312, 12616401, 15963990, 16545786, 6311375, 6311342, 6327614, 6327727, 10538589,
    2084364, 1041568, 1106957, 10037900, 1032352, 12534609, 12550993, 1371308, 5149778,
    1174700, 4961363, 1035276, 3206157, 16761840, 4129617] := by rfl
  have hc : monsterCo1GeometryVectorPoint150Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![13280, 8401904, 13248, 8430880, 8417408, 8417472, 8450624, 8405984, 8406272, 8451328,
    37968, 8478263, 15391043, 6319194, 13871476, 14790073, 8247719, 12974906, 9478477,
    15330736, 13712034, 1107574, 6397754, 8389632] := by rfl
  have hc1 : monsterCo1GeometryVectorPoint40Matrix *
    monsterCo1GeometryTransportOperatorMatrix 5 =
    monsterCo1GeometryVectorPoint150AfterSignMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![49312, 8421584, 11568080, 10518992, 12627023, 12601406, 12610767, 12617758, 12635279,
    12593198, 9438720, 12966029, 10380998, 377484, 5579650, 5579138, 259130, 8917002, 193558,
    9179142, 12704770, 4512899, 14018082, 58368]
      (monsterCo1GeometryBinaryOperatorMasks 5)
    ![49696, 8422320, 11567350, 10519162, 12692864, 12667345, 12676992, 12684145, 12701184,
    4270721, 9438860, 4511790, 10380303, 377344, 13968290, 13967778, 8647733, 529196, 8582169,
    790828, 4251309, 12966944, 5629058, 8447008] hx
    (monsterCo1GeometryBinaryOperatorMasks_decode 5) he (by decide +kernel)
  have hc2 : monsterCo1GeometryVectorPoint150AfterSignMatrix *
    monsterCo1GeometryVectorPoint40InverseMatrix =
    monsterCo1GeometryVectorPoint150AfterInverseMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![49696, 8422320, 11567350, 10519162, 12692864, 12667345, 12676992, 12684145, 12701184,
    4270721, 9438860, 4511790, 10380303, 377344, 13968290, 13967778, 8647733, 529196, 8582169,
    790828, 4251309, 12966944, 5629058, 8447008]
    ![8389616, 2427997, 9838419, 10092370, 8389918, 81, 8390287, 161, 4211725, 49152, 12519180,
    16770465, 9765376, 4130813, 12517571, 12517426, 712784, 2233360, 385025, 9761295, 49164,
    4211719, 5574481, 12518144]
    ![49312, 12616401, 15963990, 16545786, 6311375, 6311342, 6327614, 6327727, 10538589,
    2084364, 1041568, 1106957, 10037900, 1032352, 12534609, 12550993, 1371308, 5149778,
    1174700, 4961363, 1035276, 3206157, 16761840, 4129617] he hxi hf (by decide +kernel)
  have hc3 : monsterCo1GeometryVectorPoint150AfterInverseMatrix *
    monsterCo1GeometryVectorPoint127Matrix = monsterCo1GeometryVectorPoint150Matrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![49312, 12616401, 15963990, 16545786, 6311375, 6311342, 6327614, 6327727, 10538589,
    2084364, 1041568, 1106957, 10037900, 1032352, 12534609, 12550993, 1371308, 5149778,
    1174700, 4961363, 1035276, 3206157, 16761840, 4129617]
    ![3291117, 12611, 1292073, 5150, 10713103, 10733935, 9567938, 9567810, 2358812, 10746248,
    9675143, 222053, 10754264, 15948173, 5447392, 6363693, 1219807, 5667175, 16770101,
    14376503, 15873578, 9624356, 13839523, 45972]
    ![13280, 8401904, 13248, 8430880, 8417408, 8417472, 8450624, 8405984, 8406272, 8451328,
    37968, 8478263, 15391043, 6319194, 13871476, 14790073, 8247719, 12974906, 9478477,
    15330736, 13712034, 1107574, 6397754, 8389632] hf hy hc (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_line_products
    monsterCo1GeometryVectorPoint40Transport monsterCo1GeometryVectorPoint127Transport 5
    monsterCo1GeometryVectorPoint40Matrix monsterCo1GeometryVectorPoint40InverseMatrix
    monsterCo1GeometryVectorPoint127Matrix
    monsterCo1GeometryVectorPoint150AfterSignMatrix
    monsterCo1GeometryVectorPoint150AfterInverseMatrix monsterCo1GeometryVectorPoint150Matrix
    monsterCo1GeometryVectorPoint40Transport_binary
    monsterCo1GeometryVectorPoint40Transport_inverse_binary
    monsterCo1GeometryVectorPoint127Transport_binary
    hc1 hc2 hc3 v

/-- Source point 150 is the literal actual transported frame point. -/
def monsterCo1GeometryVectorPoint150 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryVectorPoint150Transport • monsterCo1GeometryBasePoint

/-- Complete binary coordinates of this literal actual source point. -/
theorem monsterCo1GeometryVectorPoint150_binary :
    monsterCo1GeometryVectorPoint150.val =
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 0] := by
  change co1BinaryAction monsterCo1GeometryVectorPoint150Transport monsterCo1GeometryBasePoint.val =
      _
  rw [monsterCo1GeometryVectorPoint150Transport_binary, monsterCo1GeometryBasePoint_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
