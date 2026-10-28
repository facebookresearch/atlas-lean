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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint002
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint014

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The literal actual two-core word for source point 46. -/
def monsterCo1GeometryVectorPoint46Transport : Co1 :=
  monsterCo1GeometryVectorPoint2Transport * monsterCo1GeometryTransportOperator 3 *
    monsterCo1GeometryVectorPoint2Transport⁻¹ * monsterCo1GeometryVectorPoint14Transport

/-- Complete displayed binary matrix of actual transport 46. -/
def monsterCo1GeometryVectorPoint46Matrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  ![![0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0],
    ![0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1],
    ![0, 0, 1, 1, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 1],
    ![0, 0, 1, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 0, 1],
    ![0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1],
    ![0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1],
    ![0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1],
    ![0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1],
    ![1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1],
    ![1, 1, 0, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1],
    ![0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1],
    ![0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0],
    ![0, 0, 1, 0, 1, 1, 0, 0, 0, 1, 1, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1],
    ![1, 1, 0, 0, 1, 1, 1, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0],
    ![0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 1],
    ![1, 0, 1, 1, 1, 0, 1, 0, 0, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1],
    ![0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1],
    ![0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1],
    ![0, 0, 1, 1, 0, 0, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0],
    ![1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 0, 0],
    ![1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 1, 1, 1, 1, 0, 1],
    ![1, 1, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]]

/-- First complete finite matrix product in literal actual transport 46. -/
def monsterCo1GeometryVectorPoint46AfterSignMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  ![![0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1],
    ![1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 1],
    ![1, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1],
    ![0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1],
    ![0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 0, 0, 0, 0, 1, 0],
    ![1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 1, 1, 1, 0, 1, 1, 0, 0, 0, 1, 0, 0, 1, 0],
    ![1, 0, 0, 1, 1, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0],
    ![1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 1],
    ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0],
    ![1, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]]

/-- Second complete finite matrix product in literal actual transport 46. -/
def monsterCo1GeometryVectorPoint46AfterInverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1, 0, 1, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1],
    ![0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
    ![0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
    ![1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
    ![0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]]

set_option maxHeartbeats 24000000 in
-- Check every entry of this finite actual transport matrix in the Lean kernel.
/-- Every column of transport 46 is its actual Conway binary action. -/
theorem monsterCo1GeometryVectorPoint46Transport_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint46Transport v =
      monsterCo1GeometryVectorPoint46Matrix *ᵥ v := by
  have hx : monsterCo1GeometryVectorPoint2Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![57504, 8441984, 8450944, 8450432, 8445968, 8446000, 8446144, 8446016, 8421584, 8405104,
    8445952, 4203168, 13684367, 1049249, 2106784, 3155872, 12811348, 12762360, 13147381,
    13392985, 9495771, 9495671, 4524557, 8389632] := by decide +kernel
  have hxi : monsterCo1GeometryVectorPoint2InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![57584, 13620028, 7336849, 6288225, 1040, 48, 1152, 192, 779, 12, 8389873, 8383473, 1987,
    769, 1617, 1441, 3343344, 10621550, 3933168, 9761135, 49164, 8406027, 3069, 1265] := by
    decide +kernel
  have hy : monsterCo1GeometryVectorPoint14Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![4129584, 11155152, 9819692, 9823788, 12572128, 12575904, 12575824, 12572368, 12598711,
    12598907, 12518640, 8338236, 212047, 196611, 11780878, 11584461, 5285275, 5330007, 6460587,
    6317671, 3966339, 3950147, 260096, 50176] := by decide +kernel
  have he : monsterCo1GeometryVectorPoint46AfterSignMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![57504, 8441984, 63360, 62848, 8445968, 8446000, 8446144, 8446016, 34000, 8405104,
    8445952, 12592811, 13667071, 1049297, 10494272, 11543344, 4406820, 4389736, 4775557,
    4987321, 9495723, 1106951, 12929149, 8389632] := by decide +kernel
  have hf : monsterCo1GeometryVectorPoint46AfterInverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![1, 2, 8388612, 8388616, 16, 32, 64, 128, 8388864, 512, 1024, 1099949, 8393216, 8352,
    8406128, 8422608, 66060, 8520070, 262668, 8913194, 1048736, 2098257, 4194828, 8388608] :=
    by decide +kernel
  have hc : monsterCo1GeometryVectorPoint46Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![4129584, 11155152, 9769516, 9773612, 12572128, 12575904, 12575824, 12572368, 12646839,
    12598907, 12518640, 8372028, 12830260, 209523, 11785966, 11592797, 9481184, 1153996,
    10656464, 2141068, 3979251, 12349491, 12842619, 50176] := by decide +kernel
  have hc1 : monsterCo1GeometryVectorPoint2Matrix * monsterCo1GeometryTransportOperatorMatrix
    3 = monsterCo1GeometryVectorPoint46AfterSignMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![57504, 8441984, 8450944, 8450432, 8445968, 8446000, 8446144, 8446016, 8421584, 8405104,
    8445952, 4203168, 13684367, 1049249, 2106784, 3155872, 12811348, 12762360, 13147381,
    13392985, 9495771, 9495671, 4524557, 8389632]
      (monsterCo1GeometryBinaryOperatorMasks 3)
    ![57504, 8441984, 63360, 62848, 8445968, 8446000, 8446144, 8446016, 34000, 8405104,
    8445952, 12592811, 13667071, 1049297, 10494272, 11543344, 4406820, 4389736, 4775557,
    4987321, 9495723, 1106951, 12929149, 8389632] hx
    (monsterCo1GeometryBinaryOperatorMasks_decode 3) he (by decide +kernel)
  have hc2 : monsterCo1GeometryVectorPoint46AfterSignMatrix *
    monsterCo1GeometryVectorPoint2InverseMatrix =
    monsterCo1GeometryVectorPoint46AfterInverseMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![57504, 8441984, 63360, 62848, 8445968, 8446000, 8446144, 8446016, 34000, 8405104,
    8445952, 12592811, 13667071, 1049297, 10494272, 11543344, 4406820, 4389736, 4775557,
    4987321, 9495723, 1106951, 12929149, 8389632]
    ![57584, 13620028, 7336849, 6288225, 1040, 48, 1152, 192, 779, 12, 8389873, 8383473, 1987,
    769, 1617, 1441, 3343344, 10621550, 3933168, 9761135, 49164, 8406027, 3069, 1265]
    ![1, 2, 8388612, 8388616, 16, 32, 64, 128, 8388864, 512, 1024, 1099949, 8393216, 8352,
    8406128, 8422608, 66060, 8520070, 262668, 8913194, 1048736, 2098257, 4194828, 8388608] he
    hxi hf (by decide +kernel)
  have hc3 : monsterCo1GeometryVectorPoint46AfterInverseMatrix *
    monsterCo1GeometryVectorPoint14Matrix = monsterCo1GeometryVectorPoint46Matrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![1, 2, 8388612, 8388616, 16, 32, 64, 128, 8388864, 512, 1024, 1099949, 8393216, 8352,
    8406128, 8422608, 66060, 8520070, 262668, 8913194, 1048736, 2098257, 4194828, 8388608]
    ![4129584, 11155152, 9819692, 9823788, 12572128, 12575904, 12575824, 12572368, 12598711,
    12598907, 12518640, 8338236, 212047, 196611, 11780878, 11584461, 5285275, 5330007, 6460587,
    6317671, 3966339, 3950147, 260096, 50176]
    ![4129584, 11155152, 9769516, 9773612, 12572128, 12575904, 12575824, 12572368, 12646839,
    12598907, 12518640, 8372028, 12830260, 209523, 11785966, 11592797, 9481184, 1153996,
    10656464, 2141068, 3979251, 12349491, 12842619, 50176] hf hy hc (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_line_products
    monsterCo1GeometryVectorPoint2Transport monsterCo1GeometryVectorPoint14Transport 3
    monsterCo1GeometryVectorPoint2Matrix monsterCo1GeometryVectorPoint2InverseMatrix
    monsterCo1GeometryVectorPoint14Matrix
    monsterCo1GeometryVectorPoint46AfterSignMatrix
    monsterCo1GeometryVectorPoint46AfterInverseMatrix monsterCo1GeometryVectorPoint46Matrix
    monsterCo1GeometryVectorPoint2Transport_binary
    monsterCo1GeometryVectorPoint2Transport_inverse_binary
    monsterCo1GeometryVectorPoint14Transport_binary
    hc1 hc2 hc3 v

/-- Source point 46 is the literal actual transported frame point. -/
def monsterCo1GeometryVectorPoint46 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryVectorPoint46Transport • monsterCo1GeometryBasePoint

/-- Complete binary coordinates of this literal actual source point. -/
theorem monsterCo1GeometryVectorPoint46_binary :
    monsterCo1GeometryVectorPoint46.val =
      ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0] := by
  change co1BinaryAction monsterCo1GeometryVectorPoint46Transport monsterCo1GeometryBasePoint.val =
      _
  rw [monsterCo1GeometryVectorPoint46Transport_binary, monsterCo1GeometryBasePoint_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
