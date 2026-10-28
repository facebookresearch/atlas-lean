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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint062

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The literal actual two-core word for source point 110. -/
def monsterCo1GeometryVectorPoint110Transport : Co1 :=
  monsterCo1GeometryVectorPoint6Transport * monsterCo1GeometryTransportOperator 5 *
    monsterCo1GeometryVectorPoint6Transport⁻¹ * monsterCo1GeometryVectorPoint62Transport

/-- Complete displayed binary matrix of actual transport 110. -/
def monsterCo1GeometryVectorPoint110Matrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![8414096, 40960, 8396800, 8430432, 20976, 45472, 8401568, 53792, 17152, 8397040, 57888,
      4227792, 8023227, 1049692, 6383924, 8350827, 3597152, 6314239, 15325439, 4186209,
      12814783, 13469883, 11592705, 8389632]

/-- First complete finite matrix product in literal actual transport 110. -/
def monsterCo1GeometryVectorPoint110AfterSignMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![49696, 8422320, 8421552, 8422064, 45472, 20976, 29600, 37712, 53792, 8401568, 57888,
      12591104, 9307395, 1376908, 15002852, 16051304, 12717060, 13176588, 12782600, 13438220,
      12585997, 12914176, 4458510, 8389632]

/-- Second complete finite matrix product in literal actual transport 110. -/
def monsterCo1GeometryVectorPoint110AfterInverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![172, 1754, 1756, 1744, 409, 504, 356, 501, 1536, 685, 941, 3840, 6881286, 8365, 7098755,
      6517026, 778240, 7213066, 974848, 7073798, 13565964, 15785984, 9494528, 8388608]

set_option maxHeartbeats 24000000 in
-- Check every entry of this finite actual transport matrix in the Lean kernel.
/-- Every column of transport 110 is its actual Conway binary action. -/
theorem monsterCo1GeometryVectorPoint110Transport_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint110Transport v =
      monsterCo1GeometryVectorPoint110Matrix *ᵥ v := by
  have hx : monsterCo1GeometryVectorPoint6Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![49312, 8421584, 8422352, 8421840, 8433728, 8409136, 8417472, 8425488, 8441984, 8400928,
    8446464, 4203168, 9307142, 1376268, 6680077, 7728653, 12782596, 13110277, 12717064,
    13372425, 12651522, 12848131, 4524557, 8389632] := by decide +kernel
  have hxi : monsterCo1GeometryVectorPoint6InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![4128768, 15007756, 5640204, 5894156, 1310, 81, 1679, 161, 10, 12, 8390652, 8383473, 1708,
    769, 1087, 1230, 712704, 10620928, 385024, 9760768, 49152, 12600332, 3069, 2044] := by
      decide +kernel
  have hy : monsterCo1GeometryVectorPoint62Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![57568, 8417472, 61632, 29600, 32, 57520, 57344, 8388672, 8438480, 41856, 57472, 12583680,
    16052155, 9471788, 3146523, 2131030, 6773501, 3236608, 12083554, 14736124, 11591776,
    3203078, 5082300, 8389632] := by decide +kernel
  have he : monsterCo1GeometryVectorPoint110AfterSignMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![49696, 8422320, 8421552, 8422064, 45472, 20976, 29600, 37712, 53792, 8401568, 57888,
    12591104, 9307395, 1376908, 15002852, 16051304, 12717060, 13176588, 12782600, 13438220,
    12585997, 12914176, 4458510, 8389632] := by rfl
  have hf : monsterCo1GeometryVectorPoint110AfterInverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![172, 1754, 1756, 1744, 409, 504, 356, 501, 1536, 685, 941, 3840, 6881286, 8365, 7098755,
    6517026, 778240, 7213066, 974848, 7073798, 13565964, 15785984, 9494528, 8388608] := by rfl
  have hc : monsterCo1GeometryVectorPoint110Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![8414096, 40960, 8396800, 8430432, 20976, 45472, 8401568, 53792, 17152, 8397040, 57888,
    4227792, 8023227, 1049692, 6383924, 8350827, 3597152, 6314239, 15325439, 4186209, 12814783,
    13469883, 11592705, 8389632] := by rfl
  have hc1 : monsterCo1GeometryVectorPoint6Matrix * monsterCo1GeometryTransportOperatorMatrix
    5 = monsterCo1GeometryVectorPoint110AfterSignMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![49312, 8421584, 8422352, 8421840, 8433728, 8409136, 8417472, 8425488, 8441984, 8400928,
    8446464, 4203168, 9307142, 1376268, 6680077, 7728653, 12782596, 13110277, 12717064,
    13372425, 12651522, 12848131, 4524557, 8389632]
      (monsterCo1GeometryBinaryOperatorMasks 5)
    ![49696, 8422320, 8421552, 8422064, 45472, 20976, 29600, 37712, 53792, 8401568, 57888,
    12591104, 9307395, 1376908, 15002852, 16051304, 12717060, 13176588, 12782600, 13438220,
    12585997, 12914176, 4458510, 8389632] hx (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    he (by decide +kernel)
  have hc2 : monsterCo1GeometryVectorPoint110AfterSignMatrix *
    monsterCo1GeometryVectorPoint6InverseMatrix =
    monsterCo1GeometryVectorPoint110AfterInverseMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![49696, 8422320, 8421552, 8422064, 45472, 20976, 29600, 37712, 53792, 8401568, 57888,
    12591104, 9307395, 1376908, 15002852, 16051304, 12717060, 13176588, 12782600, 13438220,
    12585997, 12914176, 4458510, 8389632]
    ![4128768, 15007756, 5640204, 5894156, 1310, 81, 1679, 161, 10, 12, 8390652, 8383473, 1708,
    769, 1087, 1230, 712704, 10620928, 385024, 9760768, 49152, 12600332, 3069, 2044]
    ![172, 1754, 1756, 1744, 409, 504, 356, 501, 1536, 685, 941, 3840, 6881286, 8365, 7098755,
    6517026, 778240, 7213066, 974848, 7073798, 13565964, 15785984, 9494528, 8388608] he hxi hf
    (by decide +kernel)
  have hc3 : monsterCo1GeometryVectorPoint110AfterInverseMatrix *
    monsterCo1GeometryVectorPoint62Matrix = monsterCo1GeometryVectorPoint110Matrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![172, 1754, 1756, 1744, 409, 504, 356, 501, 1536, 685, 941, 3840, 6881286, 8365, 7098755,
    6517026, 778240, 7213066, 974848, 7073798, 13565964, 15785984, 9494528, 8388608]
    ![57568, 8417472, 61632, 29600, 32, 57520, 57344, 8388672, 8438480, 41856, 57472, 12583680,
    16052155, 9471788, 3146523, 2131030, 6773501, 3236608, 12083554, 14736124, 11591776,
    3203078, 5082300, 8389632]
    ![8414096, 40960, 8396800, 8430432, 20976, 45472, 8401568, 53792, 17152, 8397040, 57888,
    4227792, 8023227, 1049692, 6383924, 8350827, 3597152, 6314239, 15325439, 4186209, 12814783,
    13469883, 11592705, 8389632] hf hy hc (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_line_products
    monsterCo1GeometryVectorPoint6Transport monsterCo1GeometryVectorPoint62Transport 5
    monsterCo1GeometryVectorPoint6Matrix monsterCo1GeometryVectorPoint6InverseMatrix
    monsterCo1GeometryVectorPoint62Matrix
    monsterCo1GeometryVectorPoint110AfterSignMatrix
    monsterCo1GeometryVectorPoint110AfterInverseMatrix monsterCo1GeometryVectorPoint110Matrix
    monsterCo1GeometryVectorPoint6Transport_binary
    monsterCo1GeometryVectorPoint6Transport_inverse_binary
    monsterCo1GeometryVectorPoint62Transport_binary
    hc1 hc2 hc3 v

/-- The displayed inverse matrix of actual source transport 110. -/
def monsterCo1GeometryVectorPoint110InverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![983136, 6747293, 5838077, 13281232, 972, 409, 664, 713, 1179, 1277, 8389485, 2416448,
      2025, 873, 358, 875, 10556263, 7308285, 10584314, 10949473, 1282324, 14454800, 3083, 877]

set_option maxHeartbeats 24000000 in
-- Check all entries of the right inverse before applying actual action injectivity.
/-- The inverse matrix is the inverse of the literal actual Conway transport. -/
theorem monsterCo1GeometryVectorPoint110Transport_inverse_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint110Transport⁻¹ v =
      monsterCo1GeometryVectorPoint110InverseMatrix *ᵥ v := by
  have hm : monsterCo1GeometryVectorPoint110Matrix = monsterCo1GeometryBinaryMaskMatrix
      ![8414096, 40960, 8396800, 8430432, 20976, 45472, 8401568, 53792, 17152, 8397040, 57888,
        4227792, 8023227, 1049692, 6383924, 8350827, 3597152, 6314239, 15325439, 4186209,
        12814783, 13469883, 11592705, 8389632] := by rfl
  have hmi : monsterCo1GeometryVectorPoint110InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
      ![983136, 6747293, 5838077, 13281232, 972, 409, 664, 713, 1179, 1277, 8389485, 2416448,
        2025, 873, 358, 875, 10556263, 7308285, 10584314, 10949473, 1282324, 14454800, 3083,
        877] := by rfl
  have hi : (1 : Matrix (Fin 24) (Fin 24) (ZMod 2)) = monsterCo1GeometryBinaryMaskMatrix
      ![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536,
        131072, 262144, 524288, 1048576, 2097152, 4194304, 8388608] := by decide +kernel
  have hc : monsterCo1GeometryVectorPoint110Matrix *
    monsterCo1GeometryVectorPoint110InverseMatrix = 1 :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
      ![8414096, 40960, 8396800, 8430432, 20976, 45472, 8401568, 53792, 17152, 8397040, 57888,
        4227792, 8023227, 1049692, 6383924, 8350827, 3597152, 6314239, 15325439, 4186209,
        12814783, 13469883, 11592705, 8389632]
      ![983136, 6747293, 5838077, 13281232, 972, 409, 664, 713, 1179, 1277, 8389485, 2416448,
        2025, 873, 358, 875, 10556263, 7308285, 10584314, 10949473, 1282324, 14454800, 3083,
        877]
      ![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536,
        131072, 262144, 524288, 1048576, 2097152, 4194304, 8388608] hm hmi hi
      (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_inv monsterCo1GeometryVectorPoint110Transport _ _
    monsterCo1GeometryVectorPoint110Transport_binary hc v

/-- Source point 110 is the literal actual transported frame point. -/
def monsterCo1GeometryVectorPoint110 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryVectorPoint110Transport • monsterCo1GeometryBasePoint

/-- Complete binary coordinates of this literal actual source point. -/
theorem monsterCo1GeometryVectorPoint110_binary :
    monsterCo1GeometryVectorPoint110.val =
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0] := by
  change co1BinaryAction monsterCo1GeometryVectorPoint110Transport monsterCo1GeometryBasePoint.val =
      _
  rw [monsterCo1GeometryVectorPoint110Transport_binary, monsterCo1GeometryBasePoint_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
