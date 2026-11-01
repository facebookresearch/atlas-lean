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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint073
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint097

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The literal actual two-core word for source point 142. -/
def monsterCo1GeometryVectorPoint142Transport : Co1 :=
  monsterCo1GeometryVectorPoint73Transport * monsterCo1GeometryTransportOperator 1 *
    monsterCo1GeometryVectorPoint73Transport⁻¹ * monsterCo1GeometryVectorPoint97Transport

/-- Complete displayed binary matrix of actual transport 142. -/
def monsterCo1GeometryVectorPoint142Matrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![8716924, 5138903, 13528970, 1013496, 46144, 57456, 57552, 8410720, 28976, 45840, 8397472,
      14013965, 45168, 8401824, 5104, 8832, 7036736, 12113001, 14847778, 8288749, 10757666,
      11804799, 3170202, 9888]

/-- First complete finite matrix product in literal actual transport 142. -/
def monsterCo1GeometryVectorPoint142AfterSignMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![1, 11002633, 2615150, 8905251, 8388736, 58384, 8447088, 8447216, 8415040, 8389968,
      8389632, 11601502, 8893140, 10502908, 2113947, 8390470, 14855717, 3417202, 7335511,
      14405133, 8388842, 3146640, 5719114, 8388784]

/-- Second complete finite matrix product in literal actual transport 142. -/
def monsterCo1GeometryVectorPoint142AfterInverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![209, 610, 692, 8389832, 16, 1056, 1088, 1152, 256, 512, 1024, 34823, 8392720, 8397472,
      8405616, 32768, 86629, 155862, 307892, 578146, 1048576, 2122966, 5145088, 8388608]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 24000000 in
-- Check every entry of this finite actual transport matrix in the Lean kernel.
/-- Every column of transport 142 is its actual Conway binary action. -/
theorem monsterCo1GeometryVectorPoint142Transport_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint142Transport v =
      monsterCo1GeometryVectorPoint142Matrix *ᵥ v := by
  have hx : monsterCo1GeometryVectorPoint73Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![8388609, 11003449, 11002462, 8906259, 8388736, 8445968, 57456, 57584, 8415040, 8389968,
    8389632, 11601278, 8893156, 2115580, 2114715, 8390470, 6471477, 11805554, 7338855, 6020157,
    8388842, 3145872, 14107252, 8388784] := by rfl
  have hxi : monsterCo1GeometryVectorPoint73InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![209, 2023537, 2024646, 975057, 8447169, 58577, 58465, 192, 8390304, 8413814, 1232,
    15990057, 45268, 8438124, 8406235, 8413574, 11464374, 9186803, 12338539, 592647, 11534458,
    1107067, 15769758, 208] := by rfl
  have hy : monsterCo1GeometryVectorPoint97Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![327820, 5167719, 5168842, 1033288, 46144, 8438480, 8438384, 29888, 28976, 45840, 8397472,
    13693100, 8848, 4096, 12960, 8832, 2105990, 3731604, 2945208, 3154570, 10757666, 11806242,
    1371308, 9888] := by rfl
  have he : monsterCo1GeometryVectorPoint142AfterSignMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![1, 11002633, 2615150, 8905251, 8388736, 58384, 8447088, 8447216, 8415040, 8389968,
    8389632, 11601502, 8893140, 10502908, 2113947, 8390470, 14855717, 3417202, 7335511,
    14405133, 8388842, 3146640, 5719114, 8388784] := by rfl
  have hf : monsterCo1GeometryVectorPoint142AfterInverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![209, 610, 692, 8389832, 16, 1056, 1088, 1152, 256, 512, 1024, 34823, 8392720, 8397472,
    8405616, 32768, 86629, 155862, 307892, 578146, 1048576, 2122966, 5145088, 8388608] := by rfl
  have hc : monsterCo1GeometryVectorPoint142Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![8716924, 5138903, 13528970, 1013496, 46144, 57456, 57552, 8410720, 28976, 45840, 8397472,
    14013965, 45168, 8401824, 5104, 8832, 7036736, 12113001, 14847778, 8288749, 10757666,
    11804799, 3170202, 9888] := by rfl
  have hc1 : monsterCo1GeometryVectorPoint73Matrix *
    monsterCo1GeometryTransportOperatorMatrix 1 =
    monsterCo1GeometryVectorPoint142AfterSignMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![8388609, 11003449, 11002462, 8906259, 8388736, 8445968, 57456, 57584, 8415040, 8389968,
    8389632, 11601278, 8893156, 2115580, 2114715, 8390470, 6471477, 11805554, 7338855, 6020157,
    8388842, 3145872, 14107252, 8388784]
      (monsterCo1GeometryBinaryOperatorMasks 1)
    ![1, 11002633, 2615150, 8905251, 8388736, 58384, 8447088, 8447216, 8415040, 8389968,
    8389632, 11601502, 8893140, 10502908, 2113947, 8390470, 14855717, 3417202, 7335511,
    14405133, 8388842, 3146640, 5719114, 8388784] hx
    (monsterCo1GeometryBinaryOperatorMasks_decode 1) he (by decide +kernel)
  have hc2 : monsterCo1GeometryVectorPoint142AfterSignMatrix *
    monsterCo1GeometryVectorPoint73InverseMatrix =
    monsterCo1GeometryVectorPoint142AfterInverseMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![1, 11002633, 2615150, 8905251, 8388736, 58384, 8447088, 8447216, 8415040, 8389968,
    8389632, 11601502, 8893140, 10502908, 2113947, 8390470, 14855717, 3417202, 7335511,
    14405133, 8388842, 3146640, 5719114, 8388784]
    ![209, 2023537, 2024646, 975057, 8447169, 58577, 58465, 192, 8390304, 8413814, 1232,
    15990057, 45268, 8438124, 8406235, 8413574, 11464374, 9186803, 12338539, 592647, 11534458,
    1107067, 15769758, 208]
    ![209, 610, 692, 8389832, 16, 1056, 1088, 1152, 256, 512, 1024, 34823, 8392720, 8397472,
    8405616, 32768, 86629, 155862, 307892, 578146, 1048576, 2122966, 5145088, 8388608] he hxi
    hf (by decide +kernel)
  have hc3 : monsterCo1GeometryVectorPoint142AfterInverseMatrix *
    monsterCo1GeometryVectorPoint97Matrix = monsterCo1GeometryVectorPoint142Matrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![209, 610, 692, 8389832, 16, 1056, 1088, 1152, 256, 512, 1024, 34823, 8392720, 8397472,
    8405616, 32768, 86629, 155862, 307892, 578146, 1048576, 2122966, 5145088, 8388608]
    ![327820, 5167719, 5168842, 1033288, 46144, 8438480, 8438384, 29888, 28976, 45840, 8397472,
    13693100, 8848, 4096, 12960, 8832, 2105990, 3731604, 2945208, 3154570, 10757666, 11806242,
    1371308, 9888]
    ![8716924, 5138903, 13528970, 1013496, 46144, 57456, 57552, 8410720, 28976, 45840, 8397472,
    14013965, 45168, 8401824, 5104, 8832, 7036736, 12113001, 14847778, 8288749, 10757666,
    11804799, 3170202, 9888] hf hy hc (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_line_products
    monsterCo1GeometryVectorPoint73Transport monsterCo1GeometryVectorPoint97Transport 1
    monsterCo1GeometryVectorPoint73Matrix monsterCo1GeometryVectorPoint73InverseMatrix
    monsterCo1GeometryVectorPoint97Matrix
    monsterCo1GeometryVectorPoint142AfterSignMatrix
    monsterCo1GeometryVectorPoint142AfterInverseMatrix monsterCo1GeometryVectorPoint142Matrix
    monsterCo1GeometryVectorPoint73Transport_binary
    monsterCo1GeometryVectorPoint73Transport_inverse_binary
    monsterCo1GeometryVectorPoint97Transport_binary
    hc1 hc2 hc3 v

/-- Source point 142 is the literal actual transported frame point. -/
def monsterCo1GeometryVectorPoint142 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryVectorPoint142Transport • monsterCo1GeometryBasePoint

/-- Complete binary coordinates of this literal actual source point. -/
theorem monsterCo1GeometryVectorPoint142_binary :
    monsterCo1GeometryVectorPoint142.val =
      ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0] := by
  change co1BinaryAction monsterCo1GeometryVectorPoint142Transport monsterCo1GeometryBasePoint.val =
      _
  rw [monsterCo1GeometryVectorPoint142Transport_binary, monsterCo1GeometryBasePoint_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
