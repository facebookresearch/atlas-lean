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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint017
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint030

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The literal actual two-core word for source point 67. -/
def monsterCo1GeometryVectorPoint67Transport : Co1 :=
  monsterCo1GeometryVectorPoint17Transport * monsterCo1GeometryTransportOperator 6 *
    monsterCo1GeometryVectorPoint17Transport⁻¹ * monsterCo1GeometryVectorPoint30Transport

/-- Complete displayed binary matrix of actual transport 67. -/
def monsterCo1GeometryVectorPoint67Matrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  ![![0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0],
    ![0, 1, 0, 1, 1, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0],
    ![1, 1, 1, 0, 1, 0, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0],
    ![1, 0, 1, 1, 0, 0, 1, 0, 1, 0, 0, 0, 1, 1, 1, 0, 0, 1, 0, 1, 0, 0, 0, 1],
    ![1, 0, 1, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0],
    ![1, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0],
    ![0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0],
    ![0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 1, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 1],
    ![0, 0, 1, 1, 1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0],
    ![0, 0, 0, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1],
    ![0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0],
    ![1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 1, 0, 0, 0, 1],
    ![0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1],
    ![1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 1],
    ![0, 0, 1, 1, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0],
    ![1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0],
    ![1, 0, 0, 1, 0, 0, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
    ![1, 0, 1, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1],
    ![0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 1, 1],
    ![1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]]

/-- First complete finite matrix product in literal actual transport 67. -/
def monsterCo1GeometryVectorPoint67AfterSignMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  ![![1, 0, 0, 1, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0],
    ![0, 1, 1, 1, 1, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 0],
    ![1, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1],
    ![1, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![1, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 1, 1],
    ![0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0],
    ![1, 1, 0, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 1],
    ![0, 1, 1, 0, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 1, 1],
    ![0, 0, 1, 0, 1, 1, 1, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0],
    ![1, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1],
    ![1, 0, 1, 0, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 1],
    ![0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 1, 1, 1],
    ![1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1],
    ![1, 0, 0, 1, 0, 0, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0],
    ![1, 1, 1, 1, 0, 1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 0, 0, 0, 1, 0, 1, 1, 0, 1],
    ![1, 1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 1, 1, 1, 1, 0, 0, 1, 0, 0, 1],
    ![0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

/-- Second complete finite matrix product in literal actual transport 67. -/
def monsterCo1GeometryVectorPoint67AfterInverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  ![![1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 0, 1],
    ![1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0],
    ![1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1],
    ![1, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1],
    ![0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![1, 1, 1, 1, 0, 0, 0, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![1, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0],
    ![0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 0, 0],
    ![1, 0, 1, 1, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 0, 1],
    ![1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 0, 1],
    ![0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 1, 0, 0, 1, 0, 1],
    ![1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 0, 1],
    ![0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1],
    ![0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1],
    ![0, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 1],
    ![0, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 1, 1, 1, 1, 0, 0],
    ![0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0],
    ![1, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1, 0],
    ![0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1]]

set_option maxHeartbeats 24000000 in
-- Check every entry of this finite actual transport matrix in the Lean kernel.
/-- Every column of transport 67 is its actual Conway binary action. -/
theorem monsterCo1GeometryVectorPoint67Transport_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint67Transport v =
      monsterCo1GeometryVectorPoint67Matrix *ᵥ v := by
  have hx : monsterCo1GeometryVectorPoint17Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![327820, 5167719, 5168842, 1041128, 37600, 8438480, 8438384, 21088, 28976, 45840, 8389632,
    13760653, 992421, 12848142, 12855971, 337569, 2107019, 15985327, 14871215, 3155591,
    10794911, 11826623, 1173645, 9888] := by decide +kernel
  have hxi : monsterCo1GeometryVectorPoint17InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![12149504, 11571197, 10413664, 11003232, 8426537, 57441, 62223, 57345, 8390304, 1008,
    8413286, 12976998, 8398845, 25590, 8402915, 8443762, 3539712, 1944173, 1040384, 8642557,
    3146496, 3140092, 4213659, 8414310] := by decide +kernel
  have hy : monsterCo1GeometryVectorPoint30Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![8388800, 8451008, 61632, 29600, 57520, 32, 8388640, 57440, 49968, 49472, 8388768,
    12615680, 8738040, 1075162, 9461879, 1996, 3212038, 15161819, 6904285, 11600565, 3203078,
    11591776, 3946495, 8389632] := by decide +kernel
  have he : monsterCo1GeometryVectorPoint67AfterSignMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![328585, 5036350, 13426067, 1040625, 8425504, 8438672, 49968, 8409568, 29664, 8433792,
    8389632, 13891659, 993276, 12979979, 12986614, 337140, 10495895, 15854133, 14740220,
    11544413, 2406217, 11826415, 9693275, 10224] := by decide +kernel
  have hf : monsterCo1GeometryVectorPoint67AfterInverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![10977329, 216697, 8595993, 10359217, 8418440, 8451471, 37257, 33207, 8422871, 8394526,
    1024, 3397886, 2028566, 12192349, 12192731, 10969526, 12121583, 8959192, 9445814, 10456956,
    4098780, 2122118, 7545009, 8413574] := by decide +kernel
  have hc : monsterCo1GeometryVectorPoint67Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![983292, 452762, 453527, 9072973, 377909, 328457, 328452, 51148, 8438636, 377400, 8388768,
    8624520, 677180, 9862520, 1465640, 9379853, 11796954, 10764715, 2114332, 8258431, 16762825,
    11585437, 16386734, 8397821] := by decide +kernel
  have hc1 : monsterCo1GeometryVectorPoint17Matrix *
    monsterCo1GeometryTransportOperatorMatrix 6 =
    monsterCo1GeometryVectorPoint67AfterSignMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![327820, 5167719, 5168842, 1041128, 37600, 8438480, 8438384, 21088, 28976, 45840, 8389632,
    13760653, 992421, 12848142, 12855971, 337569, 2107019, 15985327, 14871215, 3155591,
    10794911, 11826623, 1173645, 9888]
      (monsterCo1GeometryBinaryOperatorMasks 6)
    ![328585, 5036350, 13426067, 1040625, 8425504, 8438672, 49968, 8409568, 29664, 8433792,
    8389632, 13891659, 993276, 12979979, 12986614, 337140, 10495895, 15854133, 14740220,
    11544413, 2406217, 11826415, 9693275, 10224] hx
    (monsterCo1GeometryBinaryOperatorMasks_decode 6) he (by decide +kernel)
  have hc2 : monsterCo1GeometryVectorPoint67AfterSignMatrix *
    monsterCo1GeometryVectorPoint17InverseMatrix =
    monsterCo1GeometryVectorPoint67AfterInverseMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![328585, 5036350, 13426067, 1040625, 8425504, 8438672, 49968, 8409568, 29664, 8433792,
    8389632, 13891659, 993276, 12979979, 12986614, 337140, 10495895, 15854133, 14740220,
    11544413, 2406217, 11826415, 9693275, 10224]
    ![12149504, 11571197, 10413664, 11003232, 8426537, 57441, 62223, 57345, 8390304, 1008,
    8413286, 12976998, 8398845, 25590, 8402915, 8443762, 3539712, 1944173, 1040384, 8642557,
    3146496, 3140092, 4213659, 8414310]
    ![10977329, 216697, 8595993, 10359217, 8418440, 8451471, 37257, 33207, 8422871, 8394526,
    1024, 3397886, 2028566, 12192349, 12192731, 10969526, 12121583, 8959192, 9445814, 10456956,
    4098780, 2122118, 7545009, 8413574] he hxi hf (by decide +kernel)
  have hc3 : monsterCo1GeometryVectorPoint67AfterInverseMatrix *
    monsterCo1GeometryVectorPoint30Matrix = monsterCo1GeometryVectorPoint67Matrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![10977329, 216697, 8595993, 10359217, 8418440, 8451471, 37257, 33207, 8422871, 8394526,
    1024, 3397886, 2028566, 12192349, 12192731, 10969526, 12121583, 8959192, 9445814, 10456956,
    4098780, 2122118, 7545009, 8413574]
    ![8388800, 8451008, 61632, 29600, 57520, 32, 8388640, 57440, 49968, 49472, 8388768,
    12615680, 8738040, 1075162, 9461879, 1996, 3212038, 15161819, 6904285, 11600565, 3203078,
    11591776, 3946495, 8389632]
    ![983292, 452762, 453527, 9072973, 377909, 328457, 328452, 51148, 8438636, 377400, 8388768,
    8624520, 677180, 9862520, 1465640, 9379853, 11796954, 10764715, 2114332, 8258431, 16762825,
    11585437, 16386734, 8397821] hf hy hc (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_line_products
    monsterCo1GeometryVectorPoint17Transport monsterCo1GeometryVectorPoint30Transport 6
    monsterCo1GeometryVectorPoint17Matrix monsterCo1GeometryVectorPoint17InverseMatrix
    monsterCo1GeometryVectorPoint30Matrix
    monsterCo1GeometryVectorPoint67AfterSignMatrix
    monsterCo1GeometryVectorPoint67AfterInverseMatrix monsterCo1GeometryVectorPoint67Matrix
    monsterCo1GeometryVectorPoint17Transport_binary
    monsterCo1GeometryVectorPoint17Transport_inverse_binary
    monsterCo1GeometryVectorPoint30Transport_binary
    hc1 hc2 hc3 v

/-- The displayed inverse matrix of actual source transport 67. -/
def monsterCo1GeometryVectorPoint67InverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  ![![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1, 1, 1, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 0, 1],
    ![0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 1, 1, 0, 0, 1, 0, 1],
    ![1, 1, 1, 1, 0, 0, 0, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 1, 1, 1, 1, 1, 0, 1, 1, 0, 0, 0, 1, 1, 1, 0, 1, 1, 1, 0, 0, 1, 0, 0],
    ![1, 0, 0, 1, 0, 0, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 0, 1, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 1],
    ![0, 0, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 0, 0],
    ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1],
    ![1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0],
    ![1, 1, 1, 0, 0, 1, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 1, 0, 0, 0, 1, 1, 1, 0],
    ![0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0],
    ![0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 1, 1],
    ![1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 1, 1, 1, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 0, 1, 1, 1, 1, 1, 0, 0],
    ![1, 1, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0],
    ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1]]

set_option maxHeartbeats 24000000 in
-- Check all entries of the right inverse before applying actual action injectivity.
/-- The inverse matrix is the inverse of the literal actual Conway transport. -/
theorem monsterCo1GeometryVectorPoint67Transport_inverse_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint67Transport⁻¹ v =
      monsterCo1GeometryVectorPoint67InverseMatrix *ᵥ v := by
  have hm : monsterCo1GeometryVectorPoint67Matrix = monsterCo1GeometryBinaryMaskMatrix
      ![983292, 452762, 453527, 9072973, 377909, 328457, 328452, 51148, 8438636, 377400,
        8388768, 8624520, 677180, 9862520, 1465640, 9379853, 11796954, 10764715, 2114332,
        8258431, 16762825, 11585437, 16386734, 8397821] := by decide +kernel
  have hmi : monsterCo1GeometryVectorPoint67InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
      ![8421383, 59402, 3793767, 12149504, 10948872, 8451471, 2585022, 38281, 1942, 2032, 1408,
        13668154, 248744, 25776, 1957577, 12238847, 2194131, 7412903, 1612178, 13139760,
        10406903, 4083648, 590599, 8414214] := by decide +kernel
  have hi : (1 : Matrix (Fin 24) (Fin 24) (ZMod 2)) = monsterCo1GeometryBinaryMaskMatrix
      ![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536,
        131072, 262144, 524288, 1048576, 2097152, 4194304, 8388608] := by decide +kernel
  have hc : monsterCo1GeometryVectorPoint67Matrix *
    monsterCo1GeometryVectorPoint67InverseMatrix = 1 :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
      ![983292, 452762, 453527, 9072973, 377909, 328457, 328452, 51148, 8438636, 377400,
        8388768, 8624520, 677180, 9862520, 1465640, 9379853, 11796954, 10764715, 2114332,
        8258431, 16762825, 11585437, 16386734, 8397821]
      ![8421383, 59402, 3793767, 12149504, 10948872, 8451471, 2585022, 38281, 1942, 2032, 1408,
        13668154, 248744, 25776, 1957577, 12238847, 2194131, 7412903, 1612178, 13139760,
        10406903, 4083648, 590599, 8414214]
      ![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536,
        131072, 262144, 524288, 1048576, 2097152, 4194304, 8388608] hm hmi hi
      (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_inv monsterCo1GeometryVectorPoint67Transport _ _
    monsterCo1GeometryVectorPoint67Transport_binary hc v

/-- Source point 67 is the literal actual transported frame point. -/
def monsterCo1GeometryVectorPoint67 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryVectorPoint67Transport • monsterCo1GeometryBasePoint

/-- Complete binary coordinates of this literal actual source point. -/
theorem monsterCo1GeometryVectorPoint67_binary :
    monsterCo1GeometryVectorPoint67.val =
      ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0] := by
  change co1BinaryAction monsterCo1GeometryVectorPoint67Transport monsterCo1GeometryBasePoint.val =
      _
  rw [monsterCo1GeometryVectorPoint67Transport_binary, monsterCo1GeometryBasePoint_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
