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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint009
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint035

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The literal actual two-core word for source point 73. -/
def monsterCo1GeometryVectorPoint73Transport : Co1 :=
  monsterCo1GeometryVectorPoint9Transport * monsterCo1GeometryTransportOperator 5 *
    monsterCo1GeometryVectorPoint9Transport⁻¹ * monsterCo1GeometryVectorPoint35Transport

/-- Complete displayed binary matrix of actual transport 73. -/
def monsterCo1GeometryVectorPoint73Matrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![8388609, 11003449, 11002462, 8906259, 8388736, 8445968, 57456, 57584, 8415040, 8389968,
      8389632, 11601278, 8893156, 2115580, 2114715, 8390470, 6471477, 11805554, 7338855,
      6020157, 8388842, 3145872, 14107252, 8388784]

/-- First complete finite matrix product in literal actual transport 73. -/
def monsterCo1GeometryVectorPoint73AfterSignMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![161, 12701184, 7465959, 6416747, 1040, 8445968, 57568, 57440, 8422320, 8405392, 8389632,
      5749527, 13703324, 1066349, 2122730, 11584150, 12746548, 1208629, 14278560, 16628571,
      8390299, 3195696, 8661006, 8447008]

/-- Second complete finite matrix product in literal actual transport 73. -/
def monsterCo1GeometryVectorPoint73AfterInverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![1, 855300, 2951653, 10291615, 8447169, 8388624, 58529, 58465, 8422871, 8406171, 1024,
      3379054, 4054796, 11567676, 9496283, 10519767, 3311470, 9193554, 10047292, 3526412,
      9495761, 8389847, 16591837, 8447201]

set_option maxHeartbeats 24000000 in
-- Check every entry of this finite actual transport matrix in the Lean kernel.
/-- Every column of transport 73 is its actual Conway binary action. -/
theorem monsterCo1GeometryVectorPoint73Transport_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint73Transport v =
      monsterCo1GeometryVectorPoint73Matrix *ᵥ v := by
  have hx : monsterCo1GeometryVectorPoint9Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![161, 12635279, 15788942, 14739854, 8389648, 8446000, 8446144, 8446016, 8421584, 8405104,
    8389632, 5683319, 13637695, 9454593, 2121824, 3194960, 12811348, 1209046, 5824133,
    16563192, 1691, 11583990, 338093, 58368] := by decide +kernel
  have hxi : monsterCo1GeometryVectorPoint9InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![8388849, 9358516, 3074686, 10414792, 1040, 8388656, 8389760, 192, 8405739, 49804,
    8446161, 8381075, 8402243, 8446753, 8447601, 58753, 11731897, 10622597, 12321468, 1374176,
    49792, 16864, 4270418, 8447185] := by decide +kernel
  have hy : monsterCo1GeometryVectorPoint35Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![8388609, 4201487, 15792142, 14743566, 16, 48, 192, 64, 24784, 41072, 8389632, 13638145,
    13635087, 1107457, 10487040, 11536128, 237642, 155846, 565370, 811222, 122, 214, 65039,
    8445952] := by decide +kernel
  have he : monsterCo1GeometryVectorPoint73AfterSignMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![161, 12701184, 7465959, 6416747, 1040, 8445968, 57568, 57440, 8422320, 8405392, 8389632,
    5749527, 13703324, 1066349, 2122730, 11584150, 12746548, 1208629, 14278560, 16628571,
    8390299, 3195696, 8661006, 8447008] := by rfl
  have hf : monsterCo1GeometryVectorPoint73AfterInverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![1, 855300, 2951653, 10291615, 8447169, 8388624, 58529, 58465, 8422871, 8406171, 1024,
    3379054, 4054796, 11567676, 9496283, 10519767, 3311470, 9193554, 10047292, 3526412,
    9495761, 8389847, 16591837, 8447201] := by rfl
  have hc : monsterCo1GeometryVectorPoint73Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![8388609, 11003449, 11002462, 8906259, 8388736, 8445968, 57456, 57584, 8415040, 8389968,
    8389632, 11601278, 8893156, 2115580, 2114715, 8390470, 6471477, 11805554, 7338855, 6020157,
    8388842, 3145872, 14107252, 8388784] := by rfl
  have hc1 : monsterCo1GeometryVectorPoint9Matrix * monsterCo1GeometryTransportOperatorMatrix
    5 = monsterCo1GeometryVectorPoint73AfterSignMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![161, 12635279, 15788942, 14739854, 8389648, 8446000, 8446144, 8446016, 8421584, 8405104,
    8389632, 5683319, 13637695, 9454593, 2121824, 3194960, 12811348, 1209046, 5824133,
    16563192, 1691, 11583990, 338093, 58368]
      (monsterCo1GeometryBinaryOperatorMasks 5)
    ![161, 12701184, 7465959, 6416747, 1040, 8445968, 57568, 57440, 8422320, 8405392, 8389632,
    5749527, 13703324, 1066349, 2122730, 11584150, 12746548, 1208629, 14278560, 16628571,
    8390299, 3195696, 8661006, 8447008] hx (monsterCo1GeometryBinaryOperatorMasks_decode 5) he
    (by decide +kernel)
  have hc2 : monsterCo1GeometryVectorPoint73AfterSignMatrix *
    monsterCo1GeometryVectorPoint9InverseMatrix =
    monsterCo1GeometryVectorPoint73AfterInverseMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![161, 12701184, 7465959, 6416747, 1040, 8445968, 57568, 57440, 8422320, 8405392, 8389632,
    5749527, 13703324, 1066349, 2122730, 11584150, 12746548, 1208629, 14278560, 16628571,
    8390299, 3195696, 8661006, 8447008]
    ![8388849, 9358516, 3074686, 10414792, 1040, 8388656, 8389760, 192, 8405739, 49804,
    8446161, 8381075, 8402243, 8446753, 8447601, 58753, 11731897, 10622597, 12321468, 1374176,
    49792, 16864, 4270418, 8447185]
    ![1, 855300, 2951653, 10291615, 8447169, 8388624, 58529, 58465, 8422871, 8406171, 1024,
    3379054, 4054796, 11567676, 9496283, 10519767, 3311470, 9193554, 10047292, 3526412,
    9495761, 8389847, 16591837, 8447201] he hxi hf (by decide +kernel)
  have hc3 : monsterCo1GeometryVectorPoint73AfterInverseMatrix *
    monsterCo1GeometryVectorPoint35Matrix = monsterCo1GeometryVectorPoint73Matrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![1, 855300, 2951653, 10291615, 8447169, 8388624, 58529, 58465, 8422871, 8406171, 1024,
    3379054, 4054796, 11567676, 9496283, 10519767, 3311470, 9193554, 10047292, 3526412,
    9495761, 8389847, 16591837, 8447201]
    ![8388609, 4201487, 15792142, 14743566, 16, 48, 192, 64, 24784, 41072, 8389632, 13638145,
    13635087, 1107457, 10487040, 11536128, 237642, 155846, 565370, 811222, 122, 214, 65039,
    8445952]
    ![8388609, 11003449, 11002462, 8906259, 8388736, 8445968, 57456, 57584, 8415040, 8389968,
    8389632, 11601278, 8893156, 2115580, 2114715, 8390470, 6471477, 11805554, 7338855, 6020157,
    8388842, 3145872, 14107252, 8388784] hf hy hc (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_line_products
    monsterCo1GeometryVectorPoint9Transport monsterCo1GeometryVectorPoint35Transport 5
    monsterCo1GeometryVectorPoint9Matrix monsterCo1GeometryVectorPoint9InverseMatrix
    monsterCo1GeometryVectorPoint35Matrix
    monsterCo1GeometryVectorPoint73AfterSignMatrix
    monsterCo1GeometryVectorPoint73AfterInverseMatrix monsterCo1GeometryVectorPoint73Matrix
    monsterCo1GeometryVectorPoint9Transport_binary
    monsterCo1GeometryVectorPoint9Transport_inverse_binary
    monsterCo1GeometryVectorPoint35Transport_binary
    hc1 hc2 hc3 v

/-- The displayed inverse matrix of actual source transport 73. -/
def monsterCo1GeometryVectorPoint73InverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![209, 2023537, 2024646, 975057, 8447169, 58577, 58465, 192, 8390304, 8413814, 1232,
      15990057, 45268, 8438124, 8406235, 8413574, 11464374, 9186803, 12338539, 592647,
      11534458, 1107067, 15769758, 208]

set_option maxHeartbeats 24000000 in
-- Check all entries of the right inverse before applying actual action injectivity.
/-- The inverse matrix is the inverse of the literal actual Conway transport. -/
theorem monsterCo1GeometryVectorPoint73Transport_inverse_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint73Transport⁻¹ v =
      monsterCo1GeometryVectorPoint73InverseMatrix *ᵥ v := by
  have hm : monsterCo1GeometryVectorPoint73Matrix = monsterCo1GeometryBinaryMaskMatrix
      ![8388609, 11003449, 11002462, 8906259, 8388736, 8445968, 57456, 57584, 8415040, 8389968,
        8389632, 11601278, 8893156, 2115580, 2114715, 8390470, 6471477, 11805554, 7338855,
        6020157, 8388842, 3145872, 14107252, 8388784] := by rfl
  have hmi : monsterCo1GeometryVectorPoint73InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
      ![209, 2023537, 2024646, 975057, 8447169, 58577, 58465, 192, 8390304, 8413814, 1232,
        15990057, 45268, 8438124, 8406235, 8413574, 11464374, 9186803, 12338539, 592647,
        11534458, 1107067, 15769758, 208] := by rfl
  have hi : (1 : Matrix (Fin 24) (Fin 24) (ZMod 2)) = monsterCo1GeometryBinaryMaskMatrix
      ![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536,
        131072, 262144, 524288, 1048576, 2097152, 4194304, 8388608] := by decide +kernel
  have hc : monsterCo1GeometryVectorPoint73Matrix *
    monsterCo1GeometryVectorPoint73InverseMatrix = 1 :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
      ![8388609, 11003449, 11002462, 8906259, 8388736, 8445968, 57456, 57584, 8415040, 8389968,
        8389632, 11601278, 8893156, 2115580, 2114715, 8390470, 6471477, 11805554, 7338855,
        6020157, 8388842, 3145872, 14107252, 8388784]
      ![209, 2023537, 2024646, 975057, 8447169, 58577, 58465, 192, 8390304, 8413814, 1232,
        15990057, 45268, 8438124, 8406235, 8413574, 11464374, 9186803, 12338539, 592647,
        11534458, 1107067, 15769758, 208]
      ![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536,
        131072, 262144, 524288, 1048576, 2097152, 4194304, 8388608] hm hmi hi
      (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_inv monsterCo1GeometryVectorPoint73Transport _ _
    monsterCo1GeometryVectorPoint73Transport_binary hc v

/-- Source point 73 is the literal actual transported frame point. -/
def monsterCo1GeometryVectorPoint73 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryVectorPoint73Transport • monsterCo1GeometryBasePoint

/-- Complete binary coordinates of this literal actual source point. -/
theorem monsterCo1GeometryVectorPoint73_binary :
    monsterCo1GeometryVectorPoint73.val =
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0] := by
  change co1BinaryAction monsterCo1GeometryVectorPoint73Transport monsterCo1GeometryBasePoint.val =
      _
  rw [monsterCo1GeometryVectorPoint73Transport_binary, monsterCo1GeometryBasePoint_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
