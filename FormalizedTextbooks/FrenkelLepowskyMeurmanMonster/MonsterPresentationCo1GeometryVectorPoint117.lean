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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint073

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The literal actual two-core word for source point 117. -/
def monsterCo1GeometryVectorPoint117Transport : Co1 :=
  monsterCo1GeometryVectorPoint17Transport * monsterCo1GeometryTransportOperator 5 *
    monsterCo1GeometryVectorPoint17Transport⁻¹ * monsterCo1GeometryVectorPoint73Transport

/-- Complete displayed binary matrix of actual transport 117. -/
def monsterCo1GeometryVectorPoint117Matrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![623459, 14965833, 14964782, 975701, 8434976, 26080, 8414592, 54128, 54944, 12944,
      8389632, 15874346, 930178, 6552968, 6520671, 591252, 4885690, 8268256, 2946231, 16444144,
      10552951, 9995631, 9730480, 8421632]

/-- First complete finite matrix product in literal actual transport 117. -/
def monsterCo1GeometryVectorPoint117AfterSignMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![328320, 13621709, 13622624, 9429965, 37280, 49232, 49392, 21408, 29264, 45808, 8389632,
      13694990, 9381632, 12914189, 4532736, 8726029, 10495201, 7531209, 6548037, 11543649,
      10794169, 11826325, 9496622, 8397824]

/-- Second complete finite matrix product in literal actual transport 117. -/
def monsterCo1GeometryVectorPoint117AfterInverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![3735793, 2164937, 2164943, 2557903, 8451663, 8423351, 8423383, 8394030, 8394558, 8452047,
      1024, 4130812, 2618422, 4181005, 12569595, 12183302, 9838181, 10100117, 10878612,
      10943844, 12487852, 12029020, 16747515, 26614]

set_option maxHeartbeats 24000000 in
-- Check every entry of this finite actual transport matrix in the Lean kernel.
/-- Every column of transport 117 is its actual Conway binary action. -/
theorem monsterCo1GeometryVectorPoint117Transport_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint117Transport v =
      monsterCo1GeometryVectorPoint117Matrix *ᵥ v := by
  have hx : monsterCo1GeometryVectorPoint17Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![327820, 5167719, 5168842, 1041128, 37600, 8438480, 8438384, 21088, 28976, 45840, 8389632,
    13760653, 992421, 12848142, 12855971, 337569, 2107019, 15985327, 14871215, 3155591,
    10794911, 11826623, 1173645, 9888] := by decide +kernel
  have hxi : monsterCo1GeometryVectorPoint17InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![12149504, 11571197, 10413664, 11003232, 8426537, 57441, 62223, 57345, 8390304, 1008,
    8413286, 12976998, 8398845, 25590, 8402915, 8443762, 3539712, 1944173, 1040384, 8642557,
    3146496, 3140092, 4213659, 8414310] := by decide +kernel
  have hy : monsterCo1GeometryVectorPoint73Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![8388609, 11003449, 11002462, 8906259, 8388736, 8445968, 57456, 57584, 8415040, 8389968,
    8389632, 11601278, 8893156, 2115580, 2114715, 8390470, 6471477, 11805554, 7338855, 6020157,
    8388842, 3145872, 14107252, 8388784] := by rfl
  have he : monsterCo1GeometryVectorPoint117AfterSignMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![328320, 13621709, 13622624, 9429965, 37280, 49232, 49392, 21408, 29264, 45808, 8389632,
    13694990, 9381632, 12914189, 4532736, 8726029, 10495201, 7531209, 6548037, 11543649,
    10794169, 11826325, 9496622, 8397824] := by rfl
  have hf : monsterCo1GeometryVectorPoint117AfterInverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![3735793, 2164937, 2164943, 2557903, 8451663, 8423351, 8423383, 8394030, 8394558, 8452047,
    1024, 4130812, 2618422, 4181005, 12569595, 12183302, 9838181, 10100117, 10878612, 10943844,
    12487852, 12029020, 16747515, 26614] := by rfl
  have hc : monsterCo1GeometryVectorPoint117Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![623459, 14965833, 14964782, 975701, 8434976, 26080, 8414592, 54128, 54944, 12944,
    8389632, 15874346, 930178, 6552968, 6520671, 591252, 4885690, 8268256, 2946231, 16444144,
    10552951, 9995631, 9730480, 8421632] := by rfl
  have hc1 : monsterCo1GeometryVectorPoint17Matrix *
    monsterCo1GeometryTransportOperatorMatrix 5 =
    monsterCo1GeometryVectorPoint117AfterSignMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![327820, 5167719, 5168842, 1041128, 37600, 8438480, 8438384, 21088, 28976, 45840, 8389632,
    13760653, 992421, 12848142, 12855971, 337569, 2107019, 15985327, 14871215, 3155591,
    10794911, 11826623, 1173645, 9888]
      (monsterCo1GeometryBinaryOperatorMasks 5)
    ![328320, 13621709, 13622624, 9429965, 37280, 49232, 49392, 21408, 29264, 45808, 8389632,
    13694990, 9381632, 12914189, 4532736, 8726029, 10495201, 7531209, 6548037, 11543649,
    10794169, 11826325, 9496622, 8397824] hx (monsterCo1GeometryBinaryOperatorMasks_decode 5)
    he (by decide +kernel)
  have hc2 : monsterCo1GeometryVectorPoint117AfterSignMatrix *
    monsterCo1GeometryVectorPoint17InverseMatrix =
    monsterCo1GeometryVectorPoint117AfterInverseMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![328320, 13621709, 13622624, 9429965, 37280, 49232, 49392, 21408, 29264, 45808, 8389632,
    13694990, 9381632, 12914189, 4532736, 8726029, 10495201, 7531209, 6548037, 11543649,
    10794169, 11826325, 9496622, 8397824]
    ![12149504, 11571197, 10413664, 11003232, 8426537, 57441, 62223, 57345, 8390304, 1008,
    8413286, 12976998, 8398845, 25590, 8402915, 8443762, 3539712, 1944173, 1040384, 8642557,
    3146496, 3140092, 4213659, 8414310]
    ![3735793, 2164937, 2164943, 2557903, 8451663, 8423351, 8423383, 8394030, 8394558, 8452047,
    1024, 4130812, 2618422, 4181005, 12569595, 12183302, 9838181, 10100117, 10878612, 10943844,
    12487852, 12029020, 16747515, 26614] he hxi hf (by decide +kernel)
  have hc3 : monsterCo1GeometryVectorPoint117AfterInverseMatrix *
    monsterCo1GeometryVectorPoint73Matrix = monsterCo1GeometryVectorPoint117Matrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![3735793, 2164937, 2164943, 2557903, 8451663, 8423351, 8423383, 8394030, 8394558, 8452047,
    1024, 4130812, 2618422, 4181005, 12569595, 12183302, 9838181, 10100117, 10878612, 10943844,
    12487852, 12029020, 16747515, 26614]
    ![8388609, 11003449, 11002462, 8906259, 8388736, 8445968, 57456, 57584, 8415040, 8389968,
    8389632, 11601278, 8893156, 2115580, 2114715, 8390470, 6471477, 11805554, 7338855, 6020157,
    8388842, 3145872, 14107252, 8388784]
    ![623459, 14965833, 14964782, 975701, 8434976, 26080, 8414592, 54128, 54944, 12944,
    8389632, 15874346, 930178, 6552968, 6520671, 591252, 4885690, 8268256, 2946231, 16444144,
    10552951, 9995631, 9730480, 8421632] hf hy hc (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_line_products
    monsterCo1GeometryVectorPoint17Transport monsterCo1GeometryVectorPoint73Transport 5
    monsterCo1GeometryVectorPoint17Matrix monsterCo1GeometryVectorPoint17InverseMatrix
    monsterCo1GeometryVectorPoint73Matrix
    monsterCo1GeometryVectorPoint117AfterSignMatrix
    monsterCo1GeometryVectorPoint117AfterInverseMatrix monsterCo1GeometryVectorPoint117Matrix
    monsterCo1GeometryVectorPoint17Transport_binary
    monsterCo1GeometryVectorPoint17Transport_inverse_binary
    monsterCo1GeometryVectorPoint73Transport_binary
    hc1 hc2 hc3 v

/-- Source point 117 is the literal actual transported frame point. -/
def monsterCo1GeometryVectorPoint117 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryVectorPoint117Transport • monsterCo1GeometryBasePoint

/-- Complete binary coordinates of this literal actual source point. -/
theorem monsterCo1GeometryVectorPoint117_binary :
    monsterCo1GeometryVectorPoint117.val =
      ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0] := by
  change co1BinaryAction monsterCo1GeometryVectorPoint117Transport monsterCo1GeometryBasePoint.val =
      _
  rw [monsterCo1GeometryVectorPoint117Transport_binary, monsterCo1GeometryBasePoint_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
