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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint005
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint009

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The literal actual two-core word for source point 38. -/
def monsterCo1GeometryVectorPoint38Transport : Co1 :=
  monsterCo1GeometryVectorPoint5Transport * monsterCo1GeometryTransportOperator 1 *
    monsterCo1GeometryVectorPoint5Transport⁻¹ * monsterCo1GeometryVectorPoint9Transport

/-- Complete displayed binary matrix of actual transport 38. -/
def monsterCo1GeometryVectorPoint38Matrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  ![![1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1, 1, 1, 1, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1],
    ![0, 1, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1],
    ![0, 1, 1, 1, 0, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 1, 1, 1],
    ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 0, 0, 1, 1, 0, 1, 0],
    ![1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 0, 1, 1],
    ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1],
    ![0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1],
    ![0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0],
    ![1, 0, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 0],
    ![0, 0, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1],
    ![0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0],
    ![1, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1],
    ![0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 1, 0, 1],
    ![1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 1, 1, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]]

/-- First complete finite matrix product in literal actual transport 38. -/
def monsterCo1GeometryVectorPoint38AfterSignMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  ![![0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0],
    ![0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 1],
    ![1, 1, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 1],
    ![0, 0, 1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0],
    ![1, 1, 0, 1, 0, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 1, 0, 0, 1, 1, 1],
    ![1, 1, 0, 1, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 1, 0, 0, 1, 1, 1, 1, 0],
    ![0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1],
    ![1, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0],
    ![1, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
    ![1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 0, 1, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]]

/-- Second complete finite matrix product in literal actual transport 38. -/
def monsterCo1GeometryVectorPoint38AfterInverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 1, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1],
    ![1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1],
    ![0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
    ![0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1],
    ![0, 1, 1, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
    ![0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
    ![1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]]

set_option maxHeartbeats 24000000 in
-- Check every entry of this finite actual transport matrix in the Lean kernel.
/-- Every column of transport 38 is its actual Conway binary action. -/
theorem monsterCo1GeometryVectorPoint38Transport_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint38Transport v =
      monsterCo1GeometryVectorPoint38Matrix *ᵥ v := by
  have hx : monsterCo1GeometryVectorPoint5Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![57552, 8442048, 8450752, 45744, 57520, 8388736, 8388640, 57440, 49968, 49472, 8388768,
    12615680, 373992, 1066202, 1073783, 50908, 3418111, 15161819, 16366555, 2172254, 11535595,
    10486939, 14568157, 8389632] := by decide +kernel
  have hxi : monsterCo1GeometryVectorPoint5InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![57441, 643285, 3765294, 12185673, 225, 1056, 1073, 1088, 1366, 1008, 8389728, 13004640,
    1908, 1014, 1180, 2043, 1152766, 6127893, 2651647, 4454267, 3145968, 1098844, 2971, 1120]
    := by decide +kernel
  have hy : monsterCo1GeometryVectorPoint9Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![161, 12635279, 15788942, 14739854, 8389648, 8446000, 8446144, 8446016, 8421584, 8405104,
    8389632, 5683319, 13637695, 9454593, 2121824, 3194960, 12811348, 1209046, 5824133,
    16563192, 1691, 11583990, 338093, 58368] := by decide +kernel
  have he : monsterCo1GeometryVectorPoint38AfterSignMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![8447184, 8442048, 63168, 45744, 8447152, 8388736, 8388640, 8447072, 49968, 49472,
    8388768, 4228110, 373960, 9454298, 9461879, 50908, 3416319, 15158507, 7973115, 10559614,
    3147755, 2098587, 14572749, 8389632] := by decide +kernel
  have hf : monsterCo1GeometryVectorPoint38AfterInverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![8388609, 2, 8388612, 8, 8388624, 32, 64, 8388736, 256, 512, 1024, 613554, 5152, 8397808,
    18320, 32768, 8454854, 8520323, 262546, 8913270, 1049286, 2097462, 12582917, 8388608] := by
    decide +kernel
  have hc : monsterCo1GeometryVectorPoint38Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![58529, 12635279, 15732622, 14739854, 8445968, 8446000, 8446144, 8389696, 8421584,
    8405104, 8389632, 5884779, 13696015, 9470977, 10502288, 3194960, 7602085, 13826760,
    1603210, 13434057, 11559274, 33287, 16066434, 58368] := by decide +kernel
  have hc1 : monsterCo1GeometryVectorPoint5Matrix * monsterCo1GeometryTransportOperatorMatrix
    1 = monsterCo1GeometryVectorPoint38AfterSignMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![57552, 8442048, 8450752, 45744, 57520, 8388736, 8388640, 57440, 49968, 49472, 8388768,
    12615680, 373992, 1066202, 1073783, 50908, 3418111, 15161819, 16366555, 2172254, 11535595,
    10486939, 14568157, 8389632]
      (monsterCo1GeometryBinaryOperatorMasks 1)
    ![8447184, 8442048, 63168, 45744, 8447152, 8388736, 8388640, 8447072, 49968, 49472,
    8388768, 4228110, 373960, 9454298, 9461879, 50908, 3416319, 15158507, 7973115, 10559614,
    3147755, 2098587, 14572749, 8389632] hx (monsterCo1GeometryBinaryOperatorMasks_decode 1) he
    (by decide +kernel)
  have hc2 : monsterCo1GeometryVectorPoint38AfterSignMatrix *
    monsterCo1GeometryVectorPoint5InverseMatrix =
    monsterCo1GeometryVectorPoint38AfterInverseMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![8447184, 8442048, 63168, 45744, 8447152, 8388736, 8388640, 8447072, 49968, 49472,
    8388768, 4228110, 373960, 9454298, 9461879, 50908, 3416319, 15158507, 7973115, 10559614,
    3147755, 2098587, 14572749, 8389632]
    ![57441, 643285, 3765294, 12185673, 225, 1056, 1073, 1088, 1366, 1008, 8389728, 13004640,
    1908, 1014, 1180, 2043, 1152766, 6127893, 2651647, 4454267, 3145968, 1098844, 2971, 1120]
    ![8388609, 2, 8388612, 8, 8388624, 32, 64, 8388736, 256, 512, 1024, 613554, 5152, 8397808,
    18320, 32768, 8454854, 8520323, 262546, 8913270, 1049286, 2097462, 12582917, 8388608] he
    hxi hf (by decide +kernel)
  have hc3 : monsterCo1GeometryVectorPoint38AfterInverseMatrix *
    monsterCo1GeometryVectorPoint9Matrix = monsterCo1GeometryVectorPoint38Matrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![8388609, 2, 8388612, 8, 8388624, 32, 64, 8388736, 256, 512, 1024, 613554, 5152, 8397808,
    18320, 32768, 8454854, 8520323, 262546, 8913270, 1049286, 2097462, 12582917, 8388608]
    ![161, 12635279, 15788942, 14739854, 8389648, 8446000, 8446144, 8446016, 8421584, 8405104,
    8389632, 5683319, 13637695, 9454593, 2121824, 3194960, 12811348, 1209046, 5824133,
    16563192, 1691, 11583990, 338093, 58368]
    ![58529, 12635279, 15732622, 14739854, 8445968, 8446000, 8446144, 8389696, 8421584,
    8405104, 8389632, 5884779, 13696015, 9470977, 10502288, 3194960, 7602085, 13826760,
    1603210, 13434057, 11559274, 33287, 16066434, 58368] hf hy hc (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_line_products
    monsterCo1GeometryVectorPoint5Transport monsterCo1GeometryVectorPoint9Transport 1
    monsterCo1GeometryVectorPoint5Matrix monsterCo1GeometryVectorPoint5InverseMatrix
    monsterCo1GeometryVectorPoint9Matrix
    monsterCo1GeometryVectorPoint38AfterSignMatrix
    monsterCo1GeometryVectorPoint38AfterInverseMatrix monsterCo1GeometryVectorPoint38Matrix
    monsterCo1GeometryVectorPoint5Transport_binary
    monsterCo1GeometryVectorPoint5Transport_inverse_binary
    monsterCo1GeometryVectorPoint9Transport_binary
    hc1 hc2 hc3 v

/-- The displayed inverse matrix of actual source transport 38. -/
def monsterCo1GeometryVectorPoint38InverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  ![![1, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1, 0, 0, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0],
    ![1, 0, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 0, 1, 1, 1, 1, 0, 0, 1, 0, 1],
    ![1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 0, 1],
    ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 1, 1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![1, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0],
    ![1, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![1, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0],
    ![0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1],
    ![0, 0, 0, 1, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 1],
    ![0, 0, 1, 0, 1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 0, 0, 1, 0, 1, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0],
    ![1, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1]]

set_option maxHeartbeats 24000000 in
-- Check all entries of the right inverse before applying actual action injectivity.
/-- The inverse matrix is the inverse of the literal actual Conway transport. -/
theorem monsterCo1GeometryVectorPoint38Transport_inverse_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint38Transport⁻¹ v =
      monsterCo1GeometryVectorPoint38InverseMatrix *ᵥ v := by
  have hm : monsterCo1GeometryVectorPoint38Matrix = monsterCo1GeometryBinaryMaskMatrix
      ![58529, 12635279, 15732622, 14739854, 8445968, 8446000, 8446144, 8389696, 8421584,
        8405104, 8389632, 5884779, 13696015, 9470977, 10502288, 3194960, 7602085, 13826760,
        1603210, 13434057, 11559274, 33287, 16066434, 58368] := by decide +kernel
  have hmi : monsterCo1GeometryVectorPoint38InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
      ![241, 499185, 10992125, 9943739, 8389648, 48, 1152, 8388800, 8406395, 50460, 8447153,
        8381863, 8401555, 8447809, 57873, 8446433, 3342348, 10621200, 12321192, 1373428,
        8439056, 8406640, 4750547, 8446129] := by decide +kernel
  have hi : (1 : Matrix (Fin 24) (Fin 24) (ZMod 2)) = monsterCo1GeometryBinaryMaskMatrix
      ![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536,
        131072, 262144, 524288, 1048576, 2097152, 4194304, 8388608] := by decide +kernel
  have hc : monsterCo1GeometryVectorPoint38Matrix *
    monsterCo1GeometryVectorPoint38InverseMatrix = 1 :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
      ![58529, 12635279, 15732622, 14739854, 8445968, 8446000, 8446144, 8389696, 8421584,
        8405104, 8389632, 5884779, 13696015, 9470977, 10502288, 3194960, 7602085, 13826760,
        1603210, 13434057, 11559274, 33287, 16066434, 58368]
      ![241, 499185, 10992125, 9943739, 8389648, 48, 1152, 8388800, 8406395, 50460, 8447153,
        8381863, 8401555, 8447809, 57873, 8446433, 3342348, 10621200, 12321192, 1373428,
        8439056, 8406640, 4750547, 8446129]
      ![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536,
        131072, 262144, 524288, 1048576, 2097152, 4194304, 8388608] hm hmi hi
      (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_inv monsterCo1GeometryVectorPoint38Transport _ _
    monsterCo1GeometryVectorPoint38Transport_binary hc v

/-- Source point 38 is the literal actual transported frame point. -/
def monsterCo1GeometryVectorPoint38 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryVectorPoint38Transport • monsterCo1GeometryBasePoint

/-- Complete binary coordinates of this literal actual source point. -/
theorem monsterCo1GeometryVectorPoint38_binary :
    monsterCo1GeometryVectorPoint38.val =
      ![0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0] := by
  change co1BinaryAction monsterCo1GeometryVectorPoint38Transport monsterCo1GeometryBasePoint.val =
      _
  rw [monsterCo1GeometryVectorPoint38Transport_binary, monsterCo1GeometryBasePoint_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
