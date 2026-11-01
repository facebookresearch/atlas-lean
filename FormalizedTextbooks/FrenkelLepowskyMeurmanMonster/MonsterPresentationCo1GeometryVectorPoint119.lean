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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint067
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint073

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The literal actual two-core word for source point 119. -/
def monsterCo1GeometryVectorPoint119Transport : Co1 :=
  monsterCo1GeometryVectorPoint67Transport * monsterCo1GeometryTransportOperator 1 *
    monsterCo1GeometryVectorPoint67Transport⁻¹ * monsterCo1GeometryVectorPoint73Transport

/-- Complete displayed binary matrix of actual transport 119. -/
def monsterCo1GeometryVectorPoint119Matrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![9011974, 16739852, 16738779, 962836, 54400, 13328, 8402880, 57584, 8415040, 53984,
      8389632, 6904571, 943699, 16304585, 16272046, 8980465, 14859058, 11805381, 7338336,
      4427192, 1607391, 11536167, 1985731, 8422144]

/-- First complete finite matrix product in literal actual transport 119. -/
def monsterCo1GeometryVectorPoint119AfterSignMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![983244, 8846468, 458633, 684381, 8766485, 8717097, 328484, 51148, 8438636, 377368,
      8388768, 232886, 9064748, 9858918, 9849654, 9380925, 11797210, 10765483, 10503708,
      16646241, 8373495, 3196061, 16390590, 8398845]

/-- Second complete finite matrix product in literal actual transport 119. -/
def monsterCo1GeometryVectorPoint119AfterInverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![2614406, 10801993, 2406217, 2585862, 37273, 37289, 8451535, 128, 256, 8451983, 1024,
      2371268, 2580622, 2397501, 10785979, 2580743, 65638, 131606, 8676880, 11476229, 3664010,
      10511456, 14998214, 8390016]

set_option maxHeartbeats 24000000 in
-- Check every entry of this finite actual transport matrix in the Lean kernel.
/-- Every column of transport 119 is its actual Conway binary action. -/
theorem monsterCo1GeometryVectorPoint119Transport_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint119Transport v =
      monsterCo1GeometryVectorPoint119Matrix *ᵥ v := by
  have hx : monsterCo1GeometryVectorPoint67Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![983292, 452762, 453527, 9072973, 377909, 328457, 328452, 51148, 8438636, 377400, 8388768,
    8624520, 677180, 9862520, 1465640, 9379853, 11796954, 10764715, 2114332, 8258431, 16762825,
    11585437, 16386734, 8397821] := by decide +kernel
  have hxi : monsterCo1GeometryVectorPoint67InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![8421383, 59402, 3793767, 12149504, 10948872, 8451471, 2585022, 38281, 1942, 2032, 1408,
    13668154, 248744, 25776, 1957577, 12238847, 2194131, 7412903, 1612178, 13139760, 10406903,
    4083648, 590599, 8414214] := by decide +kernel
  have hy : monsterCo1GeometryVectorPoint73Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![8388609, 11003449, 11002462, 8906259, 8388736, 8445968, 57456, 57584, 8415040, 8389968,
    8389632, 11601278, 8893156, 2115580, 2114715, 8390470, 6471477, 11805554, 7338855, 6020157,
    8388842, 3145872, 14107252, 8388784] := by rfl
  have he : monsterCo1GeometryVectorPoint119AfterSignMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![983244, 8846468, 458633, 684381, 8766485, 8717097, 328484, 51148, 8438636, 377368,
    8388768, 232886, 9064748, 9858918, 9849654, 9380925, 11797210, 10765483, 10503708,
    16646241, 8373495, 3196061, 16390590, 8398845] := by rfl
  have hf : monsterCo1GeometryVectorPoint119AfterInverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![2614406, 10801993, 2406217, 2585862, 37273, 37289, 8451535, 128, 256, 8451983, 1024,
    2371268, 2580622, 2397501, 10785979, 2580743, 65638, 131606, 8676880, 11476229, 3664010,
    10511456, 14998214, 8390016] := by rfl
  have hc : monsterCo1GeometryVectorPoint119Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![9011974, 16739852, 16738779, 962836, 54400, 13328, 8402880, 57584, 8415040, 53984,
    8389632, 6904571, 943699, 16304585, 16272046, 8980465, 14859058, 11805381, 7338336,
    4427192, 1607391, 11536167, 1985731, 8422144] := by rfl
  have hc1 : monsterCo1GeometryVectorPoint67Matrix *
    monsterCo1GeometryTransportOperatorMatrix 1 =
    monsterCo1GeometryVectorPoint119AfterSignMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![983292, 452762, 453527, 9072973, 377909, 328457, 328452, 51148, 8438636, 377400, 8388768,
    8624520, 677180, 9862520, 1465640, 9379853, 11796954, 10764715, 2114332, 8258431, 16762825,
    11585437, 16386734, 8397821]
      (monsterCo1GeometryBinaryOperatorMasks 1)
    ![983244, 8846468, 458633, 684381, 8766485, 8717097, 328484, 51148, 8438636, 377368,
    8388768, 232886, 9064748, 9858918, 9849654, 9380925, 11797210, 10765483, 10503708,
    16646241, 8373495, 3196061, 16390590, 8398845] hx
    (monsterCo1GeometryBinaryOperatorMasks_decode 1) he (by decide +kernel)
  have hc2 : monsterCo1GeometryVectorPoint119AfterSignMatrix *
    monsterCo1GeometryVectorPoint67InverseMatrix =
    monsterCo1GeometryVectorPoint119AfterInverseMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![983244, 8846468, 458633, 684381, 8766485, 8717097, 328484, 51148, 8438636, 377368,
    8388768, 232886, 9064748, 9858918, 9849654, 9380925, 11797210, 10765483, 10503708,
    16646241, 8373495, 3196061, 16390590, 8398845]
    ![8421383, 59402, 3793767, 12149504, 10948872, 8451471, 2585022, 38281, 1942, 2032, 1408,
    13668154, 248744, 25776, 1957577, 12238847, 2194131, 7412903, 1612178, 13139760, 10406903,
    4083648, 590599, 8414214]
    ![2614406, 10801993, 2406217, 2585862, 37273, 37289, 8451535, 128, 256, 8451983, 1024,
    2371268, 2580622, 2397501, 10785979, 2580743, 65638, 131606, 8676880, 11476229, 3664010,
    10511456, 14998214, 8390016] he hxi hf (by decide +kernel)
  have hc3 : monsterCo1GeometryVectorPoint119AfterInverseMatrix *
    monsterCo1GeometryVectorPoint73Matrix = monsterCo1GeometryVectorPoint119Matrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![2614406, 10801993, 2406217, 2585862, 37273, 37289, 8451535, 128, 256, 8451983, 1024,
    2371268, 2580622, 2397501, 10785979, 2580743, 65638, 131606, 8676880, 11476229, 3664010,
    10511456, 14998214, 8390016]
    ![8388609, 11003449, 11002462, 8906259, 8388736, 8445968, 57456, 57584, 8415040, 8389968,
    8389632, 11601278, 8893156, 2115580, 2114715, 8390470, 6471477, 11805554, 7338855, 6020157,
    8388842, 3145872, 14107252, 8388784]
    ![9011974, 16739852, 16738779, 962836, 54400, 13328, 8402880, 57584, 8415040, 53984,
    8389632, 6904571, 943699, 16304585, 16272046, 8980465, 14859058, 11805381, 7338336,
    4427192, 1607391, 11536167, 1985731, 8422144] hf hy hc (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_line_products
    monsterCo1GeometryVectorPoint67Transport monsterCo1GeometryVectorPoint73Transport 1
    monsterCo1GeometryVectorPoint67Matrix monsterCo1GeometryVectorPoint67InverseMatrix
    monsterCo1GeometryVectorPoint73Matrix
    monsterCo1GeometryVectorPoint119AfterSignMatrix
    monsterCo1GeometryVectorPoint119AfterInverseMatrix monsterCo1GeometryVectorPoint119Matrix
    monsterCo1GeometryVectorPoint67Transport_binary
    monsterCo1GeometryVectorPoint67Transport_inverse_binary
    monsterCo1GeometryVectorPoint73Transport_binary
    hc1 hc2 hc3 v

/-- Source point 119 is the literal actual transported frame point. -/
def monsterCo1GeometryVectorPoint119 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryVectorPoint119Transport • monsterCo1GeometryBasePoint

/-- Complete binary coordinates of this literal actual source point. -/
theorem monsterCo1GeometryVectorPoint119_binary :
    monsterCo1GeometryVectorPoint119.val =
      ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0, 1, 0] := by
  change co1BinaryAction monsterCo1GeometryVectorPoint119Transport monsterCo1GeometryBasePoint.val =
      _
  rw [monsterCo1GeometryVectorPoint119Transport_binary, monsterCo1GeometryBasePoint_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
