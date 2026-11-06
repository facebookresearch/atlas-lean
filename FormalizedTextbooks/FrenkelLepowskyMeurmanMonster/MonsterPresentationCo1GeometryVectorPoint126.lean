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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint013
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint081

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The literal actual two-core word for source point 126. -/
def monsterCo1GeometryVectorPoint126Transport : Co1 :=
  monsterCo1GeometryVectorPoint13Transport * monsterCo1GeometryTransportOperator 5 *
    monsterCo1GeometryVectorPoint13Transport⁻¹ * monsterCo1GeometryVectorPoint81Transport

/-- Complete displayed binary matrix of actual transport 126. -/
def monsterCo1GeometryVectorPoint126Matrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![931477, 9338981, 14190725, 14191237, 8880386, 8414096, 459733, 8415040, 8880389, 57584,
      8388784, 13291804, 590593, 971059, 16268606, 16268857, 13740517, 4545117, 4287896,
      13501028, 10359743, 8575837, 13254368, 33712]

/-- First complete finite matrix product in literal actual transport 126. -/
def monsterCo1GeometryVectorPoint126AfterSignMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![12517811, 11142035, 5507624, 5507620, 5424, 13248, 8441984, 12288, 8442528, 12928,
      8389632, 5585571, 11154783, 12531711, 12684932, 12668552, 77952, 9556096, 131331,
      16136509, 197184, 7486127, 67599, 50816]

/-- Second complete finite matrix product in literal actual transport 126. -/
def monsterCo1GeometryVectorPoint126AfterInverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![9815181, 9815566, 1323563, 1323559, 13267, 672, 8451983, 512, 8451791, 128, 1024,
      1325231, 9819276, 9823756, 9745731, 9729987, 66176, 8570816, 1114156, 12000313, 327724,
      2091066, 5517487, 8389248]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 24000000 in
-- Check every entry of this finite actual transport matrix in the Lean kernel.
/-- Every column of transport 126 is its actual Conway binary action. -/
theorem monsterCo1GeometryVectorPoint126Transport_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint126Transport v =
      monsterCo1GeometryVectorPoint126Matrix *ᵥ v := by
  have hx : monsterCo1GeometryVectorPoint13Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![4129008, 2752592, 5572775, 5572779, 5392, 12608, 53792, 12928, 53248, 12288, 8389632,
    5520044, 2765852, 4142140, 4230635, 4214631, 78336, 1168044, 131340, 7813623, 197199,
    7551081, 2048, 50176] := by decide +kernel
  have hxi : monsterCo1GeometryVectorPoint13InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![12518067, 11141779, 1312808, 1312804, 54194, 13251, 8441986, 12291, 8442530, 12931,
    8438412, 4194304, 50060, 49548, 8405483, 8422247, 77955, 8704686, 144268, 8966308, 196812,
    9175352, 4261903, 8439436] := by decide +kernel
  have hy : monsterCo1GeometryVectorPoint81Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![1040, 13648, 4864, 4352, 57504, 58400, 57456, 57584, 8413856, 8415040, 8388784, 9620777,
    471428, 8414214, 10495244, 2138555, 5320277, 12967738, 13622218, 5986653, 1091053, 1074337,
    9577173, 8389632] := by rfl
  have he : monsterCo1GeometryVectorPoint126AfterSignMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![12517811, 11142035, 5507624, 5507620, 5424, 13248, 8441984, 12288, 8442528, 12928,
    8389632, 5585571, 11154783, 12531711, 12684932, 12668552, 77952, 9556096, 131331, 16136509,
    197184, 7486127, 67599, 50816] := by rfl
  have hf : monsterCo1GeometryVectorPoint126AfterInverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![9815181, 9815566, 1323563, 1323559, 13267, 672, 8451983, 512, 8451791, 128, 1024,
    1325231, 9819276, 9823756, 9745731, 9729987, 66176, 8570816, 1114156, 12000313, 327724,
    2091066, 5517487, 8389248] := by rfl
  have hc : monsterCo1GeometryVectorPoint126Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![931477, 9338981, 14190725, 14191237, 8880386, 8414096, 459733, 8415040, 8880389, 57584,
    8388784, 13291804, 590593, 971059, 16268606, 16268857, 13740517, 4545117, 4287896,
    13501028, 10359743, 8575837, 13254368, 33712] := by rfl
  have hc1 : monsterCo1GeometryVectorPoint13Matrix *
    monsterCo1GeometryTransportOperatorMatrix 5 =
    monsterCo1GeometryVectorPoint126AfterSignMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![4129008, 2752592, 5572775, 5572779, 5392, 12608, 53792, 12928, 53248, 12288, 8389632,
    5520044, 2765852, 4142140, 4230635, 4214631, 78336, 1168044, 131340, 7813623, 197199,
    7551081, 2048, 50176]
      (monsterCo1GeometryBinaryOperatorMasks 5)
    ![12517811, 11142035, 5507624, 5507620, 5424, 13248, 8441984, 12288, 8442528, 12928,
    8389632, 5585571, 11154783, 12531711, 12684932, 12668552, 77952, 9556096, 131331, 16136509,
    197184, 7486127, 67599, 50816] hx (monsterCo1GeometryBinaryOperatorMasks_decode 5) he (by
    decide +kernel)
  have hc2 : monsterCo1GeometryVectorPoint126AfterSignMatrix *
    monsterCo1GeometryVectorPoint13InverseMatrix =
    monsterCo1GeometryVectorPoint126AfterInverseMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![12517811, 11142035, 5507624, 5507620, 5424, 13248, 8441984, 12288, 8442528, 12928,
    8389632, 5585571, 11154783, 12531711, 12684932, 12668552, 77952, 9556096, 131331, 16136509,
    197184, 7486127, 67599, 50816]
    ![12518067, 11141779, 1312808, 1312804, 54194, 13251, 8441986, 12291, 8442530, 12931,
    8438412, 4194304, 50060, 49548, 8405483, 8422247, 77955, 8704686, 144268, 8966308, 196812,
    9175352, 4261903, 8439436]
    ![9815181, 9815566, 1323563, 1323559, 13267, 672, 8451983, 512, 8451791, 128, 1024,
    1325231, 9819276, 9823756, 9745731, 9729987, 66176, 8570816, 1114156, 12000313, 327724,
    2091066, 5517487, 8389248] he hxi hf (by decide +kernel)
  have hc3 : monsterCo1GeometryVectorPoint126AfterInverseMatrix *
    monsterCo1GeometryVectorPoint81Matrix = monsterCo1GeometryVectorPoint126Matrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![9815181, 9815566, 1323563, 1323559, 13267, 672, 8451983, 512, 8451791, 128, 1024,
    1325231, 9819276, 9823756, 9745731, 9729987, 66176, 8570816, 1114156, 12000313, 327724,
    2091066, 5517487, 8389248]
    ![1040, 13648, 4864, 4352, 57504, 58400, 57456, 57584, 8413856, 8415040, 8388784, 9620777,
    471428, 8414214, 10495244, 2138555, 5320277, 12967738, 13622218, 5986653, 1091053, 1074337,
    9577173, 8389632]
    ![931477, 9338981, 14190725, 14191237, 8880386, 8414096, 459733, 8415040, 8880389, 57584,
    8388784, 13291804, 590593, 971059, 16268606, 16268857, 13740517, 4545117, 4287896,
    13501028, 10359743, 8575837, 13254368, 33712] hf hy hc (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_line_products
    monsterCo1GeometryVectorPoint13Transport monsterCo1GeometryVectorPoint81Transport 5
    monsterCo1GeometryVectorPoint13Matrix monsterCo1GeometryVectorPoint13InverseMatrix
    monsterCo1GeometryVectorPoint81Matrix
    monsterCo1GeometryVectorPoint126AfterSignMatrix
    monsterCo1GeometryVectorPoint126AfterInverseMatrix monsterCo1GeometryVectorPoint126Matrix
    monsterCo1GeometryVectorPoint13Transport_binary
    monsterCo1GeometryVectorPoint13Transport_inverse_binary
    monsterCo1GeometryVectorPoint81Transport_binary
    hc1 hc2 hc3 v

/-- Source point 126 is the literal actual transported frame point. -/
def monsterCo1GeometryVectorPoint126 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryVectorPoint126Transport • monsterCo1GeometryBasePoint

/-- Complete binary coordinates of this literal actual source point. -/
theorem monsterCo1GeometryVectorPoint126_binary :
    monsterCo1GeometryVectorPoint126.val =
      ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 0, 1, 1, 0] := by
  change co1BinaryAction monsterCo1GeometryVectorPoint126Transport monsterCo1GeometryBasePoint.val =
      _
  rw [monsterCo1GeometryVectorPoint126Transport_binary, monsterCo1GeometryBasePoint_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
