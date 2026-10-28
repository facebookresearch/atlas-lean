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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint057

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The literal actual two-core word for source point 103. -/
def monsterCo1GeometryVectorPoint103Transport : Co1 :=
  monsterCo1GeometryVectorPoint40Transport * monsterCo1GeometryTransportOperator 6 *
    monsterCo1GeometryVectorPoint40Transport⁻¹ * monsterCo1GeometryVectorPoint57Transport

/-- Complete displayed binary matrix of actual transport 103. -/
def monsterCo1GeometryVectorPoint103Matrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![12742900, 512439, 3461874, 10528438, 13220888, 5171932, 9160921, 827113, 13528892,
      13188248, 1340051, 1137975, 14160, 13455965, 14569630, 14570142, 559991, 465191,
      13584682, 13630074, 8428583, 9419895, 14222665, 8868352]

/-- First complete finite matrix product in literal actual transport 103. -/
def monsterCo1GeometryVectorPoint103AfterSignMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![8438240, 33280, 3178890, 2130764, 12758976, 12733345, 12742144, 4360897, 12766656,
      12724593, 9438918, 4709079, 10380998, 377033, 13967633, 13968145, 8647733, 528662,
      193558, 791056, 4447570, 13033174, 14018033, 8446992]

/-- Second complete finite matrix product in literal actual transport 103. -/
def monsterCo1GeometryVectorPoint103AfterInverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![8339843, 12566578, 209818, 3155638, 13139712, 4749870, 540114, 3619596, 4765758,
      13155872, 3346720, 2174862, 4096, 9894444, 10127634, 10111250, 1371308, 7512594, 262144,
      8705296, 13455500, 11257890, 10848400, 12518942]

set_option maxHeartbeats 24000000 in
-- Check every entry of this finite actual transport matrix in the Lean kernel.
/-- Every column of transport 103 is its actual Conway binary action. -/
theorem monsterCo1GeometryVectorPoint103Transport_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint103Transport v =
      monsterCo1GeometryVectorPoint103Matrix *ᵥ v := by
  have hx : monsterCo1GeometryVectorPoint40Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![49312, 8421584, 11568080, 10518992, 12627023, 12601406, 12610767, 12617758, 12635279,
    12593198, 9438720, 12966029, 10380998, 377484, 5579650, 5579138, 259130, 8917002, 193558,
    9179142, 12704770, 4512899, 14018082, 58368] := by decide +kernel
  have hxi : monsterCo1GeometryVectorPoint40InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![8389616, 2427997, 9838419, 10092370, 8389918, 81, 8390287, 161, 4211725, 49152, 12519180,
    16770465, 9765376, 4130813, 12517571, 12517426, 712784, 2233360, 385025, 9761295, 49164,
    4211719, 5574481, 12518144] := by decide +kernel
  have hy : monsterCo1GeometryVectorPoint57Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![1041, 513571, 11006217, 11007854, 8447136, 58400, 8447088, 8447216, 26272, 25408,
    8388784, 14099015, 14160, 1552, 8256, 8768, 5352069, 12938698, 13584682, 6000589, 1106445,
    9495041, 12910962, 1200] := by decide +kernel
  have he : monsterCo1GeometryVectorPoint103AfterSignMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![8438240, 33280, 3178890, 2130764, 12758976, 12733345, 12742144, 4360897, 12766656,
    12724593, 9438918, 4709079, 10380998, 377033, 13967633, 13968145, 8647733, 528662, 193558,
    791056, 4447570, 13033174, 14018033, 8446992] := by rfl
  have hf : monsterCo1GeometryVectorPoint103AfterInverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![8339843, 12566578, 209818, 3155638, 13139712, 4749870, 540114, 3619596, 4765758,
    13155872, 3346720, 2174862, 4096, 9894444, 10127634, 10111250, 1371308, 7512594, 262144,
    8705296, 13455500, 11257890, 10848400, 12518942] := by rfl
  have hc : monsterCo1GeometryVectorPoint103Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![12742900, 512439, 3461874, 10528438, 13220888, 5171932, 9160921, 827113, 13528892,
    13188248, 1340051, 1137975, 14160, 13455965, 14569630, 14570142, 559991, 465191, 13584682,
    13630074, 8428583, 9419895, 14222665, 8868352] := by rfl
  have hc1 : monsterCo1GeometryVectorPoint40Matrix *
    monsterCo1GeometryTransportOperatorMatrix 6 =
    monsterCo1GeometryVectorPoint103AfterSignMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![49312, 8421584, 11568080, 10518992, 12627023, 12601406, 12610767, 12617758, 12635279,
    12593198, 9438720, 12966029, 10380998, 377484, 5579650, 5579138, 259130, 8917002, 193558,
    9179142, 12704770, 4512899, 14018082, 58368]
      (monsterCo1GeometryBinaryOperatorMasks 6)
    ![8438240, 33280, 3178890, 2130764, 12758976, 12733345, 12742144, 4360897, 12766656,
    12724593, 9438918, 4709079, 10380998, 377033, 13967633, 13968145, 8647733, 528662, 193558,
    791056, 4447570, 13033174, 14018033, 8446992] hx
    (monsterCo1GeometryBinaryOperatorMasks_decode 6) he (by decide +kernel)
  have hc2 : monsterCo1GeometryVectorPoint103AfterSignMatrix *
    monsterCo1GeometryVectorPoint40InverseMatrix =
    monsterCo1GeometryVectorPoint103AfterInverseMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![8438240, 33280, 3178890, 2130764, 12758976, 12733345, 12742144, 4360897, 12766656,
    12724593, 9438918, 4709079, 10380998, 377033, 13967633, 13968145, 8647733, 528662, 193558,
    791056, 4447570, 13033174, 14018033, 8446992]
    ![8389616, 2427997, 9838419, 10092370, 8389918, 81, 8390287, 161, 4211725, 49152, 12519180,
    16770465, 9765376, 4130813, 12517571, 12517426, 712784, 2233360, 385025, 9761295, 49164,
    4211719, 5574481, 12518144]
    ![8339843, 12566578, 209818, 3155638, 13139712, 4749870, 540114, 3619596, 4765758,
    13155872, 3346720, 2174862, 4096, 9894444, 10127634, 10111250, 1371308, 7512594, 262144,
    8705296, 13455500, 11257890, 10848400, 12518942] he hxi hf (by decide +kernel)
  have hc3 : monsterCo1GeometryVectorPoint103AfterInverseMatrix *
    monsterCo1GeometryVectorPoint57Matrix = monsterCo1GeometryVectorPoint103Matrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![8339843, 12566578, 209818, 3155638, 13139712, 4749870, 540114, 3619596, 4765758,
    13155872, 3346720, 2174862, 4096, 9894444, 10127634, 10111250, 1371308, 7512594, 262144,
    8705296, 13455500, 11257890, 10848400, 12518942]
    ![1041, 513571, 11006217, 11007854, 8447136, 58400, 8447088, 8447216, 26272, 25408,
    8388784, 14099015, 14160, 1552, 8256, 8768, 5352069, 12938698, 13584682, 6000589, 1106445,
    9495041, 12910962, 1200]
    ![12742900, 512439, 3461874, 10528438, 13220888, 5171932, 9160921, 827113, 13528892,
    13188248, 1340051, 1137975, 14160, 13455965, 14569630, 14570142, 559991, 465191, 13584682,
    13630074, 8428583, 9419895, 14222665, 8868352] hf hy hc (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_line_products
    monsterCo1GeometryVectorPoint40Transport monsterCo1GeometryVectorPoint57Transport 6
    monsterCo1GeometryVectorPoint40Matrix monsterCo1GeometryVectorPoint40InverseMatrix
    monsterCo1GeometryVectorPoint57Matrix
    monsterCo1GeometryVectorPoint103AfterSignMatrix
    monsterCo1GeometryVectorPoint103AfterInverseMatrix monsterCo1GeometryVectorPoint103Matrix
    monsterCo1GeometryVectorPoint40Transport_binary
    monsterCo1GeometryVectorPoint40Transport_inverse_binary
    monsterCo1GeometryVectorPoint57Transport_binary
    hc1 hc2 hc3 v

/-- Source point 103 is the literal actual transported frame point. -/
def monsterCo1GeometryVectorPoint103 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryVectorPoint103Transport • monsterCo1GeometryBasePoint

/-- Complete binary coordinates of this literal actual source point. -/
theorem monsterCo1GeometryVectorPoint103_binary :
    monsterCo1GeometryVectorPoint103.val =
      ![0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0] := by
  change co1BinaryAction monsterCo1GeometryVectorPoint103Transport monsterCo1GeometryBasePoint.val =
      _
  rw [monsterCo1GeometryVectorPoint103Transport_binary, monsterCo1GeometryBasePoint_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
