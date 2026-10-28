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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint030
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint051

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The literal actual two-core word for source point 99. -/
def monsterCo1GeometryVectorPoint99Transport : Co1 :=
  monsterCo1GeometryVectorPoint30Transport * monsterCo1GeometryTransportOperator 1 *
    monsterCo1GeometryVectorPoint30Transport⁻¹ * monsterCo1GeometryVectorPoint51Transport

/-- Complete displayed binary matrix of actual transport 99. -/
def monsterCo1GeometryVectorPoint99Matrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![327820, 5167719, 5175402, 1033288, 37600, 8438480, 8438384, 21088, 28976, 45840, 8397472,
      8470178, 49888, 8401056, 5792, 8398464, 2148347, 7559663, 6462319, 3196247, 2397247,
      3429407, 5304847, 9888]

/-- First complete finite matrix product in literal actual transport 99. -/
def monsterCo1GeometryVectorPoint99AfterSignMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![8388800, 63424, 8451264, 29600, 8447152, 32, 8388640, 8447072, 49968, 49472, 8388768,
      4228110, 348376, 1074650, 1073783, 1996, 3211302, 15158507, 6900989, 3211669, 11593478,
      3204960, 3944703, 8389632]

/-- Second complete finite matrix product in literal actual transport 99. -/
def monsterCo1GeometryVectorPoint99AfterInverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![1, 8388610, 8388612, 8, 8388624, 32, 64, 8388736, 256, 512, 1024, 618337, 8392736, 10224,
      18320, 32768, 65606, 8520643, 8651570, 524326, 9437286, 10485862, 12582918, 8388608]

set_option maxHeartbeats 24000000 in
-- Check every entry of this finite actual transport matrix in the Lean kernel.
/-- Every column of transport 99 is its actual Conway binary action. -/
theorem monsterCo1GeometryVectorPoint99Transport_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint99Transport v =
      monsterCo1GeometryVectorPoint99Matrix *ᵥ v := by
  have hx : monsterCo1GeometryVectorPoint30Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![8388800, 8451008, 61632, 29600, 57520, 32, 8388640, 57440, 49968, 49472, 8388768,
    12615680, 8738040, 1075162, 9461879, 1996, 3212038, 15161819, 6904285, 11600565, 3203078,
    11591776, 3946495, 8389632] := by decide +kernel
  have hxi : monsterCo1GeometryVectorPoint30InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![58465, 648966, 3793767, 12149504, 241, 32, 1057, 1088, 1942, 2032, 8388704, 12860069,
    1252, 1334, 1500, 1131, 1115367, 6260357, 2651759, 4322539, 3187834, 1090714, 3083, 96] :=
    by decide +kernel
  have hy : monsterCo1GeometryVectorPoint51Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![327820, 5176519, 5168842, 1033288, 46144, 8438480, 8438384, 29888, 28976, 45840, 8397472,
    9763490, 8398480, 4096, 8402592, 8398464, 10495878, 12122004, 11335096, 11543946, 2396210,
    3428370, 5306018, 9888] := by decide +kernel
  have he : monsterCo1GeometryVectorPoint99AfterSignMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![8388800, 63424, 8451264, 29600, 8447152, 32, 8388640, 8447072, 49968, 49472, 8388768,
    4228110, 348376, 1074650, 1073783, 1996, 3211302, 15158507, 6900989, 3211669, 11593478,
    3204960, 3944703, 8389632] := by rfl
  have hf : monsterCo1GeometryVectorPoint99AfterInverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![1, 8388610, 8388612, 8, 8388624, 32, 64, 8388736, 256, 512, 1024, 618337, 8392736, 10224,
    18320, 32768, 65606, 8520643, 8651570, 524326, 9437286, 10485862, 12582918, 8388608] := by rfl
  have hc : monsterCo1GeometryVectorPoint99Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![327820, 5167719, 5175402, 1033288, 37600, 8438480, 8438384, 21088, 28976, 45840, 8397472,
    8470178, 49888, 8401056, 5792, 8398464, 2148347, 7559663, 6462319, 3196247, 2397247,
    3429407, 5304847, 9888] := by rfl
  have hc1 : monsterCo1GeometryVectorPoint30Matrix *
    monsterCo1GeometryTransportOperatorMatrix 1 =
    monsterCo1GeometryVectorPoint99AfterSignMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![8388800, 8451008, 61632, 29600, 57520, 32, 8388640, 57440, 49968, 49472, 8388768,
    12615680, 8738040, 1075162, 9461879, 1996, 3212038, 15161819, 6904285, 11600565, 3203078,
    11591776, 3946495, 8389632]
      (monsterCo1GeometryBinaryOperatorMasks 1)
    ![8388800, 63424, 8451264, 29600, 8447152, 32, 8388640, 8447072, 49968, 49472, 8388768,
    4228110, 348376, 1074650, 1073783, 1996, 3211302, 15158507, 6900989, 3211669, 11593478,
    3204960, 3944703, 8389632] hx (monsterCo1GeometryBinaryOperatorMasks_decode 1) he (by
    decide +kernel)
  have hc2 : monsterCo1GeometryVectorPoint99AfterSignMatrix *
    monsterCo1GeometryVectorPoint30InverseMatrix =
    monsterCo1GeometryVectorPoint99AfterInverseMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![8388800, 63424, 8451264, 29600, 8447152, 32, 8388640, 8447072, 49968, 49472, 8388768,
    4228110, 348376, 1074650, 1073783, 1996, 3211302, 15158507, 6900989, 3211669, 11593478,
    3204960, 3944703, 8389632]
    ![58465, 648966, 3793767, 12149504, 241, 32, 1057, 1088, 1942, 2032, 8388704, 12860069,
    1252, 1334, 1500, 1131, 1115367, 6260357, 2651759, 4322539, 3187834, 1090714, 3083, 96]
    ![1, 8388610, 8388612, 8, 8388624, 32, 64, 8388736, 256, 512, 1024, 618337, 8392736, 10224,
    18320, 32768, 65606, 8520643, 8651570, 524326, 9437286, 10485862, 12582918, 8388608] he hxi
    hf (by decide +kernel)
  have hc3 : monsterCo1GeometryVectorPoint99AfterInverseMatrix *
    monsterCo1GeometryVectorPoint51Matrix = monsterCo1GeometryVectorPoint99Matrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![1, 8388610, 8388612, 8, 8388624, 32, 64, 8388736, 256, 512, 1024, 618337, 8392736, 10224,
    18320, 32768, 65606, 8520643, 8651570, 524326, 9437286, 10485862, 12582918, 8388608]
    ![327820, 5176519, 5168842, 1033288, 46144, 8438480, 8438384, 29888, 28976, 45840, 8397472,
    9763490, 8398480, 4096, 8402592, 8398464, 10495878, 12122004, 11335096, 11543946, 2396210,
    3428370, 5306018, 9888]
    ![327820, 5167719, 5175402, 1033288, 37600, 8438480, 8438384, 21088, 28976, 45840, 8397472,
    8470178, 49888, 8401056, 5792, 8398464, 2148347, 7559663, 6462319, 3196247, 2397247,
    3429407, 5304847, 9888] hf hy hc (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_line_products
    monsterCo1GeometryVectorPoint30Transport monsterCo1GeometryVectorPoint51Transport 1
    monsterCo1GeometryVectorPoint30Matrix monsterCo1GeometryVectorPoint30InverseMatrix
    monsterCo1GeometryVectorPoint51Matrix
    monsterCo1GeometryVectorPoint99AfterSignMatrix
    monsterCo1GeometryVectorPoint99AfterInverseMatrix monsterCo1GeometryVectorPoint99Matrix
    monsterCo1GeometryVectorPoint30Transport_binary
    monsterCo1GeometryVectorPoint30Transport_inverse_binary
    monsterCo1GeometryVectorPoint51Transport_binary
    hc1 hc2 hc3 v

/-- Source point 99 is the literal actual transported frame point. -/
def monsterCo1GeometryVectorPoint99 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryVectorPoint99Transport • monsterCo1GeometryBasePoint

/-- Complete binary coordinates of this literal actual source point. -/
theorem monsterCo1GeometryVectorPoint99_binary :
    monsterCo1GeometryVectorPoint99.val =
      ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0] := by
  change co1BinaryAction monsterCo1GeometryVectorPoint99Transport monsterCo1GeometryBasePoint.val =
      _
  rw [monsterCo1GeometryVectorPoint99Transport_binary, monsterCo1GeometryBasePoint_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
