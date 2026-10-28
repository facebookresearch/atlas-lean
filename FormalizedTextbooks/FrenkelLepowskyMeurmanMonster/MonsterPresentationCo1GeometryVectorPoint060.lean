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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint008
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint029

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The literal actual two-core word for source point 60. -/
def monsterCo1GeometryVectorPoint60Transport : Co1 :=
  monsterCo1GeometryVectorPoint8Transport * monsterCo1GeometryTransportOperator 5 *
    monsterCo1GeometryVectorPoint8Transport⁻¹ * monsterCo1GeometryVectorPoint29Transport

/-- Complete displayed binary matrix of actual transport 60. -/
def monsterCo1GeometryVectorPoint60Matrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  ![![1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![1, 1, 0, 1, 0, 0, 0, 1, 0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 1, 1, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 1, 1, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 1],
    ![1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0],
    ![0, 1, 0, 0, 0, 1, 0, 0, 1, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0],
    ![1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1],
    ![0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![1, 1, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0],
    ![1, 1, 1, 0, 1, 1, 1, 1, 0, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0],
    ![0, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 1, 0, 1],
    ![1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 0],
    ![0, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 0, 0, 1, 0, 1, 0, 1, 1, 0, 0],
    ![1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1],
    ![1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0],
    ![1, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 0, 0, 1, 1, 1, 0, 0, 1, 0],
    ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]]

/-- First complete finite matrix product in literal actual transport 60. -/
def monsterCo1GeometryVectorPoint60AfterSignMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  ![![1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1],
    ![1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 1, 1, 1, 1],
    ![1, 1, 0, 1, 0, 1, 1, 1, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 1],
    ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 1, 1],
    ![0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1],
    ![0, 0, 1, 1, 1, 1, 0, 1, 0, 0, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 0, 1, 0],
    ![0, 0, 1, 1, 1, 0, 0, 1, 0, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 0, 1, 0],
    ![1, 1, 1, 0, 1, 1, 1, 0, 0, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 1],
    ![1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1],
    ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]]

/-- Second complete finite matrix product in literal actual transport 60. -/
def monsterCo1GeometryVectorPoint60AfterInverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  ![![1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0],
    ![0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0],
    ![0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 1, 1, 0, 1, 0],
    ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 1, 0, 1],
    ![0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0],
    ![0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1],
    ![0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]]

set_option maxHeartbeats 24000000 in
-- Check every entry of this finite actual transport matrix in the Lean kernel.
/-- Every column of transport 60 is its actual Conway binary action. -/
theorem monsterCo1GeometryVectorPoint60Transport_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint60Transport v =
      monsterCo1GeometryVectorPoint60Matrix *ᵥ v := by
  have hx : monsterCo1GeometryVectorPoint8Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![57345, 4201487, 7346190, 6297614, 8445968, 8446000, 8446144, 8446016, 8421584, 8405104,
    58368, 338093, 8442496, 58016, 49568, 50080, 12811348, 12762360, 13147381, 13392985,
    9495771, 9495671, 4203168, 8445952] := by decide +kernel
  have hxi : monsterCo1GeometryVectorPoint8InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![57585, 13573938, 7281567, 6232943, 8388624, 48, 8388736, 192, 17152, 49152, 58608,
    4131825, 8401856, 58112, 8446544, 8446368, 3343344, 10618478, 3933168, 9700719, 12, 1035,
    4203504, 8446192] := by decide +kernel
  have hy : monsterCo1GeometryVectorPoint29Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![57552, 8442048, 8450752, 45744, 57520, 1152, 8388640, 57440, 49968, 49472, 8388768,
    2599355, 8736856, 1074042, 9462999, 876, 3430303, 15161819, 7986139, 10593822, 3196587,
    10503371, 14568157, 8389632] := by decide +kernel
  have he : monsterCo1GeometryVectorPoint60AfterSignMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![8445985, 12655648, 15800423, 14751979, 8446000, 8445968, 57568, 57440, 8422320, 8405392,
    8447008, 8661006, 53280, 8446592, 49952, 49440, 12746548, 12827928, 4824252, 5069980,
    9495671, 9495771, 12591104, 57376] := by decide +kernel
  have hf : monsterCo1GeometryVectorPoint60AfterInverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![8446145, 4987905, 7084074, 6035478, 32, 16, 8446080, 8446016, 8422064, 8405360, 8447168,
    8131635, 8400896, 8437952, 32960, 16576, 11698240, 11616384, 6821918, 5511214, 2097152,
    1048576, 12591104, 57536] := by decide +kernel
  have hc : monsterCo1GeometryVectorPoint60Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![8388689, 2371211, 8711360, 9751264, 1152, 57520, 57505, 8388833, 8438396, 9455607, 57377,
    1257888, 1390370, 9470971, 8446764, 1082519, 7855351, 11818312, 8200683, 3488382, 10503371,
    3196587, 5123495, 58497] := by decide +kernel
  have hc1 : monsterCo1GeometryVectorPoint8Matrix * monsterCo1GeometryTransportOperatorMatrix
    5 = monsterCo1GeometryVectorPoint60AfterSignMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![57345, 4201487, 7346190, 6297614, 8445968, 8446000, 8446144, 8446016, 8421584, 8405104,
    58368, 338093, 8442496, 58016, 49568, 50080, 12811348, 12762360, 13147381, 13392985,
    9495771, 9495671, 4203168, 8445952]
      (monsterCo1GeometryBinaryOperatorMasks 5)
    ![8445985, 12655648, 15800423, 14751979, 8446000, 8445968, 57568, 57440, 8422320, 8405392,
    8447008, 8661006, 53280, 8446592, 49952, 49440, 12746548, 12827928, 4824252, 5069980,
    9495671, 9495771, 12591104, 57376] hx (monsterCo1GeometryBinaryOperatorMasks_decode 5) he
    (by decide +kernel)
  have hc2 : monsterCo1GeometryVectorPoint60AfterSignMatrix *
    monsterCo1GeometryVectorPoint8InverseMatrix =
    monsterCo1GeometryVectorPoint60AfterInverseMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![8445985, 12655648, 15800423, 14751979, 8446000, 8445968, 57568, 57440, 8422320, 8405392,
    8447008, 8661006, 53280, 8446592, 49952, 49440, 12746548, 12827928, 4824252, 5069980,
    9495671, 9495771, 12591104, 57376]
    ![57585, 13573938, 7281567, 6232943, 8388624, 48, 8388736, 192, 17152, 49152, 58608,
    4131825, 8401856, 58112, 8446544, 8446368, 3343344, 10618478, 3933168, 9700719, 12, 1035,
    4203504, 8446192]
    ![8446145, 4987905, 7084074, 6035478, 32, 16, 8446080, 8446016, 8422064, 8405360, 8447168,
    8131635, 8400896, 8437952, 32960, 16576, 11698240, 11616384, 6821918, 5511214, 2097152,
    1048576, 12591104, 57536] he hxi hf (by decide +kernel)
  have hc3 : monsterCo1GeometryVectorPoint60AfterInverseMatrix *
    monsterCo1GeometryVectorPoint29Matrix = monsterCo1GeometryVectorPoint60Matrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![8446145, 4987905, 7084074, 6035478, 32, 16, 8446080, 8446016, 8422064, 8405360, 8447168,
    8131635, 8400896, 8437952, 32960, 16576, 11698240, 11616384, 6821918, 5511214, 2097152,
    1048576, 12591104, 57536]
    ![57552, 8442048, 8450752, 45744, 57520, 1152, 8388640, 57440, 49968, 49472, 8388768,
    2599355, 8736856, 1074042, 9462999, 876, 3430303, 15161819, 7986139, 10593822, 3196587,
    10503371, 14568157, 8389632]
    ![8388689, 2371211, 8711360, 9751264, 1152, 57520, 57505, 8388833, 8438396, 9455607, 57377,
    1257888, 1390370, 9470971, 8446764, 1082519, 7855351, 11818312, 8200683, 3488382, 10503371,
    3196587, 5123495, 58497] hf hy hc (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_line_products
    monsterCo1GeometryVectorPoint8Transport monsterCo1GeometryVectorPoint29Transport 5
    monsterCo1GeometryVectorPoint8Matrix monsterCo1GeometryVectorPoint8InverseMatrix
    monsterCo1GeometryVectorPoint29Matrix
    monsterCo1GeometryVectorPoint60AfterSignMatrix
    monsterCo1GeometryVectorPoint60AfterInverseMatrix monsterCo1GeometryVectorPoint60Matrix
    monsterCo1GeometryVectorPoint8Transport_binary
    monsterCo1GeometryVectorPoint8Transport_inverse_binary
    monsterCo1GeometryVectorPoint29Transport_binary
    hc1 hc2 hc3 v

/-- Source point 60 is the literal actual transported frame point. -/
def monsterCo1GeometryVectorPoint60 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryVectorPoint60Transport • monsterCo1GeometryBasePoint

/-- Complete binary coordinates of this literal actual source point. -/
theorem monsterCo1GeometryVectorPoint60_binary :
    monsterCo1GeometryVectorPoint60.val =
      ![0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0] := by
  change co1BinaryAction monsterCo1GeometryVectorPoint60Transport monsterCo1GeometryBasePoint.val =
      _
  rw [monsterCo1GeometryVectorPoint60Transport_binary, monsterCo1GeometryBasePoint_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
