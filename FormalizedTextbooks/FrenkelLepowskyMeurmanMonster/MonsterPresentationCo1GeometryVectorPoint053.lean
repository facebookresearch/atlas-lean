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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint021

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The literal actual two-core word for source point 53. -/
def monsterCo1GeometryVectorPoint53Transport : Co1 :=
  monsterCo1GeometryVectorPoint2Transport * monsterCo1GeometryTransportOperator 2 *
    monsterCo1GeometryVectorPoint2Transport⁻¹ * monsterCo1GeometryVectorPoint21Transport

/-- Complete displayed binary matrix of actual transport 53. -/
def monsterCo1GeometryVectorPoint53Matrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  ![![0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1],
    ![1, 1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 0, 1, 1],
    ![1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 1],
    ![1, 0, 0, 1, 1, 1, 0, 0, 1, 1, 1, 0, 0, 1, 1, 1, 0, 1, 0, 1, 0, 0, 0, 1],
    ![0, 0, 1, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1],
    ![0, 0, 1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0],
    ![0, 0, 1, 1, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0],
    ![0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 0, 0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0],
    ![1, 0, 0, 0, 1, 1, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0],
    ![1, 1, 0, 0, 0, 1, 1, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 1],
    ![0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1],
    ![1, 1, 0, 0, 0, 1, 0, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 0, 1],
    ![0, 1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1],
    ![1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1],
    ![1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 0],
    ![0, 1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 1, 0],
    ![1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 1],
    ![0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 1, 1, 0],
    ![0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 1, 1, 0],
    ![1, 0, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 1, 1, 0, 0, 1, 0],
    ![1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1],
    ![1, 1, 0, 0, 0, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 0, 1],
    ![1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 0, 1, 1, 1, 1, 0, 1, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

/-- First complete finite matrix product in literal actual transport 53. -/
def monsterCo1GeometryVectorPoint53AfterSignMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  ![![0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
    ![1, 1, 1, 1, 0, 1, 0, 0, 0, 1, 1, 1, 0, 1, 1, 1, 0, 0, 0, 0, 1, 0, 1, 0],
    ![1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
    ![0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
    ![0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0],
    ![0, 0, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1],
    ![0, 0, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 1],
    ![1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 0, 0, 1, 0, 0, 1, 1],
    ![1, 0, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 0, 0, 1, 1],
    ![1, 1, 0, 1, 1, 1, 1, 0, 0, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0],
    ![1, 1, 1, 0, 1, 0, 1, 1, 0, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0],
    ![1, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]]

/-- Second complete finite matrix product in literal actual transport 53. -/
def monsterCo1GeometryVectorPoint53AfterInverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
    ![0, 1, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
    ![0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
    ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
    ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
    ![1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]]

set_option maxHeartbeats 24000000 in
-- Check every entry of this finite actual transport matrix in the Lean kernel.
/-- Every column of transport 53 is its actual Conway binary action. -/
theorem monsterCo1GeometryVectorPoint53Transport_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint53Transport v =
      monsterCo1GeometryVectorPoint53Matrix *ᵥ v := by
  have hx : monsterCo1GeometryVectorPoint2Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![57504, 8441984, 8450944, 8450432, 8445968, 8446000, 8446144, 8446016, 8421584, 8405104,
    8445952, 4203168, 13684367, 1049249, 2106784, 3155872, 12811348, 12762360, 13147381,
    13392985, 9495771, 9495671, 4524557, 8389632] := by decide +kernel
  have hxi : monsterCo1GeometryVectorPoint2InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![57584, 13620028, 7336849, 6288225, 1040, 48, 1152, 192, 779, 12, 8389873, 8383473, 1987,
    769, 1617, 1441, 3343344, 10621550, 3933168, 9761135, 49164, 8406027, 3069, 1265] := by
    decide +kernel
  have hy : monsterCo1GeometryVectorPoint21Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![8753212, 13536263, 9073289, 9093529, 8754796, 349372, 365724, 378620, 328401, 12889667,
    8717452, 1435523, 16017024, 2397375, 15764017, 5541566, 13459633, 11328136, 11213486,
    552115, 10584547, 10559859, 5482265, 9888] := by decide +kernel
  have he : monsterCo1GeometryVectorPoint53AfterSignMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![57504, 54400, 63360, 62848, 8445968, 8446000, 8446144, 8446016, 34000, 17520, 8445952,
    4203181, 5303855, 1049089, 2106864, 3155792, 12804004, 12754344, 13155749, 13402025,
    1107067, 1107159, 4532749, 8389632] := by decide +kernel
  have hf : monsterCo1GeometryVectorPoint53AfterInverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![1, 8388610, 8388612, 8388616, 16, 32, 64, 128, 8388864, 8389120, 1024, 3205120, 5888,
    8432, 16528, 32864, 65638, 131226, 262298, 524390, 1049601, 2098177, 4195073, 8388608] :=
    by decide +kernel
  have hc : monsterCo1GeometryVectorPoint53Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![8753212, 13544103, 9065513, 9103161, 8754796, 349372, 365724, 378620, 337009, 12880099,
    8717452, 9819939, 11587230, 10748943, 7396001, 5525150, 9002527, 6866822, 7276448, 5001757,
    10556755, 10597827, 1547191, 9888] := by decide +kernel
  have hc1 : monsterCo1GeometryVectorPoint2Matrix * monsterCo1GeometryTransportOperatorMatrix
    2 = monsterCo1GeometryVectorPoint53AfterSignMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![57504, 8441984, 8450944, 8450432, 8445968, 8446000, 8446144, 8446016, 8421584, 8405104,
    8445952, 4203168, 13684367, 1049249, 2106784, 3155872, 12811348, 12762360, 13147381,
    13392985, 9495771, 9495671, 4524557, 8389632]
      (monsterCo1GeometryBinaryOperatorMasks 2)
    ![57504, 54400, 63360, 62848, 8445968, 8446000, 8446144, 8446016, 34000, 17520, 8445952,
    4203181, 5303855, 1049089, 2106864, 3155792, 12804004, 12754344, 13155749, 13402025,
    1107067, 1107159, 4532749, 8389632] hx (monsterCo1GeometryBinaryOperatorMasks_decode 2) he
    (by decide +kernel)
  have hc2 : monsterCo1GeometryVectorPoint53AfterSignMatrix *
    monsterCo1GeometryVectorPoint2InverseMatrix =
    monsterCo1GeometryVectorPoint53AfterInverseMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![57504, 54400, 63360, 62848, 8445968, 8446000, 8446144, 8446016, 34000, 17520, 8445952,
    4203181, 5303855, 1049089, 2106864, 3155792, 12804004, 12754344, 13155749, 13402025,
    1107067, 1107159, 4532749, 8389632]
    ![57584, 13620028, 7336849, 6288225, 1040, 48, 1152, 192, 779, 12, 8389873, 8383473, 1987,
    769, 1617, 1441, 3343344, 10621550, 3933168, 9761135, 49164, 8406027, 3069, 1265]
    ![1, 8388610, 8388612, 8388616, 16, 32, 64, 128, 8388864, 8389120, 1024, 3205120, 5888,
    8432, 16528, 32864, 65638, 131226, 262298, 524390, 1049601, 2098177, 4195073, 8388608] he
    hxi hf (by decide +kernel)
  have hc3 : monsterCo1GeometryVectorPoint53AfterInverseMatrix *
    monsterCo1GeometryVectorPoint21Matrix = monsterCo1GeometryVectorPoint53Matrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![1, 8388610, 8388612, 8388616, 16, 32, 64, 128, 8388864, 8389120, 1024, 3205120, 5888,
    8432, 16528, 32864, 65638, 131226, 262298, 524390, 1049601, 2098177, 4195073, 8388608]
    ![8753212, 13536263, 9073289, 9093529, 8754796, 349372, 365724, 378620, 328401, 12889667,
    8717452, 1435523, 16017024, 2397375, 15764017, 5541566, 13459633, 11328136, 11213486,
    552115, 10584547, 10559859, 5482265, 9888]
    ![8753212, 13544103, 9065513, 9103161, 8754796, 349372, 365724, 378620, 337009, 12880099,
    8717452, 9819939, 11587230, 10748943, 7396001, 5525150, 9002527, 6866822, 7276448, 5001757,
    10556755, 10597827, 1547191, 9888] hf hy hc (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_line_products
    monsterCo1GeometryVectorPoint2Transport monsterCo1GeometryVectorPoint21Transport 2
    monsterCo1GeometryVectorPoint2Matrix monsterCo1GeometryVectorPoint2InverseMatrix
    monsterCo1GeometryVectorPoint21Matrix
    monsterCo1GeometryVectorPoint53AfterSignMatrix
    monsterCo1GeometryVectorPoint53AfterInverseMatrix monsterCo1GeometryVectorPoint53Matrix
    monsterCo1GeometryVectorPoint2Transport_binary
    monsterCo1GeometryVectorPoint2Transport_inverse_binary
    monsterCo1GeometryVectorPoint21Transport_binary
    hc1 hc2 hc3 v

/-- The displayed inverse matrix of actual source transport 53. -/
def monsterCo1GeometryVectorPoint53InverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  ![![0, 0, 1, 0, 1, 0, 0, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0],
    ![1, 0, 1, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 0, 0, 0, 1],
    ![1, 0, 1, 0, 0, 1, 0, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1],
    ![0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 0, 0, 1, 1, 1, 1, 1, 0, 1, 1],
    ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1],
    ![0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![1, 1, 1, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
    ![1, 1, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1],
    ![0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1],
    ![1, 1, 0, 1, 1, 1, 0, 0, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1],
    ![1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 0],
    ![1, 1, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0],
    ![1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 1, 1, 0, 0, 0],
    ![0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 0, 0],
    ![1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 1, 1, 0, 1, 0, 0, 0, 1, 1, 1, 0, 1, 1, 0],
    ![0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![1, 0, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0, 1, 0, 0, 0, 1],
    ![1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1],
    ![1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0]]

set_option maxHeartbeats 24000000 in
-- Check all entries of the right inverse before applying actual action injectivity.
/-- The inverse matrix is the inverse of the literal actual Conway transport. -/
theorem monsterCo1GeometryVectorPoint53Transport_inverse_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint53Transport⁻¹ v =
      monsterCo1GeometryVectorPoint53InverseMatrix *ᵥ v := by
  have hm : monsterCo1GeometryVectorPoint53Matrix = monsterCo1GeometryBinaryMaskMatrix
      ![8753212, 13544103, 9065513, 9103161, 8754796, 349372, 365724, 378620, 337009, 12880099,
        8717452, 9819939, 11587230, 10748943, 7396001, 5525150, 9002527, 6866822, 7276448,
        5001757, 10556755, 10597827, 1547191, 9888] := by decide +kernel
  have hmi : monsterCo1GeometryVectorPoint53InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
      ![8869780, 1092096, 9093309, 11384357, 14620496, 58432, 16725194, 57584, 8389645, 871,
        2105580, 14807827, 11593622, 10495803, 5190843, 5230747, 2004377, 12319812, 3736320,
        7220845, 8423264, 9022717, 14666619, 2106397] := by decide +kernel
  have hi : (1 : Matrix (Fin 24) (Fin 24) (ZMod 2)) = monsterCo1GeometryBinaryMaskMatrix
      ![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536,
        131072, 262144, 524288, 1048576, 2097152, 4194304, 8388608] := by decide +kernel
  have hc : monsterCo1GeometryVectorPoint53Matrix *
    monsterCo1GeometryVectorPoint53InverseMatrix = 1 :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
      ![8753212, 13544103, 9065513, 9103161, 8754796, 349372, 365724, 378620, 337009, 12880099,
        8717452, 9819939, 11587230, 10748943, 7396001, 5525150, 9002527, 6866822, 7276448,
        5001757, 10556755, 10597827, 1547191, 9888]
      ![8869780, 1092096, 9093309, 11384357, 14620496, 58432, 16725194, 57584, 8389645, 871,
        2105580, 14807827, 11593622, 10495803, 5190843, 5230747, 2004377, 12319812, 3736320,
        7220845, 8423264, 9022717, 14666619, 2106397]
      ![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536,
        131072, 262144, 524288, 1048576, 2097152, 4194304, 8388608] hm hmi hi
      (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_inv monsterCo1GeometryVectorPoint53Transport _ _
    monsterCo1GeometryVectorPoint53Transport_binary hc v

/-- Source point 53 is the literal actual transported frame point. -/
def monsterCo1GeometryVectorPoint53 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryVectorPoint53Transport • monsterCo1GeometryBasePoint

/-- Complete binary coordinates of this literal actual source point. -/
theorem monsterCo1GeometryVectorPoint53_binary :
    monsterCo1GeometryVectorPoint53.val =
      ![0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0] := by
  change co1BinaryAction monsterCo1GeometryVectorPoint53Transport monsterCo1GeometryBasePoint.val =
      _
  rw [monsterCo1GeometryVectorPoint53Transport_binary, monsterCo1GeometryBasePoint_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
