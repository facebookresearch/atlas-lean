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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint012
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint073

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The literal actual two-core word for source point 116. -/
def monsterCo1GeometryVectorPoint116Transport : Co1 :=
  monsterCo1GeometryVectorPoint12Transport * monsterCo1GeometryTransportOperator 5 *
    monsterCo1GeometryVectorPoint12Transport⁻¹ * monsterCo1GeometryVectorPoint73Transport

/-- Complete displayed binary matrix of actual transport 116. -/
def monsterCo1GeometryVectorPoint116Matrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![8388609, 11003449, 2580537, 8906357, 459605, 25110, 8413814, 483620, 484596, 8881381,
      34407, 11601176, 962610, 8748930, 8748261, 623652, 11222356, 10459150, 5063032, 10182463,
      4653627, 8290595, 7502346, 8388784]

/-- First complete finite matrix product in literal actual transport 116. -/
def monsterCo1GeometryVectorPoint116AfterSignMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![128, 8450752, 53856, 8446144, 37280, 49232, 49392, 21408, 29264, 45808, 8192, 4198432,
      9430880, 4537389, 4536448, 329261, 10495201, 7531209, 6548037, 11543649, 10794169,
      11826325, 13694990, 8389632]

/-- Second complete finite matrix product in literal actual transport 116. -/
def monsterCo1GeometryVectorPoint116AfterInverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![1, 2, 2034, 1039, 1615, 1975, 2007, 1326, 1854, 1999, 1014, 3079, 10982336, 16770032,
      16745456, 3768560, 5654126, 5916062, 6637215, 6702447, 8275111, 7816279, 12567536,
      8388608]

set_option maxHeartbeats 24000000 in
-- Check every entry of this finite actual transport matrix in the Lean kernel.
/-- Every column of transport 116 is its actual Conway binary action. -/
theorem monsterCo1GeometryVectorPoint116Transport_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint116Transport v =
      monsterCo1GeometryVectorPoint116Matrix *ᵥ v := by
  have hx : monsterCo1GeometryVectorPoint12Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![128, 8450752, 8442048, 57568, 37600, 8438480, 8438384, 21088, 28976, 45840, 8397472,
    12587008, 1041989, 4471982, 4470787, 328737, 2107019, 15985327, 14871215, 3155591,
    10794911, 11826623, 13760653, 8389632] := by decide +kernel
  have hxi : monsterCo1GeometryVectorPoint12InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![12150534, 7383031, 2025057, 2614625, 1065, 97, 783, 1, 1696, 1008, 8389734, 13004640,
    2045, 1014, 2019, 1906, 3539712, 6128234, 1040385, 4454386, 3146496, 7283185, 2971, 1126]
    := by decide +kernel
  have hy : monsterCo1GeometryVectorPoint73Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![8388609, 11003449, 11002462, 8906259, 8388736, 8445968, 57456, 57584, 8415040, 8389968,
    8389632, 11601278, 8893156, 2115580, 2114715, 8390470, 6471477, 11805554, 7338855, 6020157,
    8388842, 3145872, 14107252, 8388784] := by rfl
  have he : monsterCo1GeometryVectorPoint116AfterSignMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![128, 8450752, 53856, 8446144, 37280, 49232, 49392, 21408, 29264, 45808, 8192, 4198432,
    9430880, 4537389, 4536448, 329261, 10495201, 7531209, 6548037, 11543649, 10794169,
    11826325, 13694990, 8389632] := by rfl
  have hf : monsterCo1GeometryVectorPoint116AfterInverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![1, 2, 2034, 1039, 1615, 1975, 2007, 1326, 1854, 1999, 1014, 3079, 10982336, 16770032,
    16745456, 3768560, 5654126, 5916062, 6637215, 6702447, 8275111, 7816279, 12567536, 8388608]
    := by rfl
  have hc : monsterCo1GeometryVectorPoint116Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![8388609, 11003449, 2580537, 8906357, 459605, 25110, 8413814, 483620, 484596, 8881381,
    34407, 11601176, 962610, 8748930, 8748261, 623652, 11222356, 10459150, 5063032, 10182463,
    4653627, 8290595, 7502346, 8388784] := by rfl
  have hc1 : monsterCo1GeometryVectorPoint12Matrix *
    monsterCo1GeometryTransportOperatorMatrix 5 =
    monsterCo1GeometryVectorPoint116AfterSignMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![128, 8450752, 8442048, 57568, 37600, 8438480, 8438384, 21088, 28976, 45840, 8397472,
    12587008, 1041989, 4471982, 4470787, 328737, 2107019, 15985327, 14871215, 3155591,
    10794911, 11826623, 13760653, 8389632]
      (monsterCo1GeometryBinaryOperatorMasks 5)
    ![128, 8450752, 53856, 8446144, 37280, 49232, 49392, 21408, 29264, 45808, 8192, 4198432,
    9430880, 4537389, 4536448, 329261, 10495201, 7531209, 6548037, 11543649, 10794169,
    11826325, 13694990, 8389632] hx (monsterCo1GeometryBinaryOperatorMasks_decode 5) he (by
    decide +kernel)
  have hc2 : monsterCo1GeometryVectorPoint116AfterSignMatrix *
    monsterCo1GeometryVectorPoint12InverseMatrix =
    monsterCo1GeometryVectorPoint116AfterInverseMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![128, 8450752, 53856, 8446144, 37280, 49232, 49392, 21408, 29264, 45808, 8192, 4198432,
    9430880, 4537389, 4536448, 329261, 10495201, 7531209, 6548037, 11543649, 10794169,
    11826325, 13694990, 8389632]
    ![12150534, 7383031, 2025057, 2614625, 1065, 97, 783, 1, 1696, 1008, 8389734, 13004640,
    2045, 1014, 2019, 1906, 3539712, 6128234, 1040385, 4454386, 3146496, 7283185, 2971, 1126]
    ![1, 2, 2034, 1039, 1615, 1975, 2007, 1326, 1854, 1999, 1014, 3079, 10982336, 16770032,
    16745456, 3768560, 5654126, 5916062, 6637215, 6702447, 8275111, 7816279, 12567536, 8388608]
    he hxi hf (by decide +kernel)
  have hc3 : monsterCo1GeometryVectorPoint116AfterInverseMatrix *
    monsterCo1GeometryVectorPoint73Matrix = monsterCo1GeometryVectorPoint116Matrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![1, 2, 2034, 1039, 1615, 1975, 2007, 1326, 1854, 1999, 1014, 3079, 10982336, 16770032,
    16745456, 3768560, 5654126, 5916062, 6637215, 6702447, 8275111, 7816279, 12567536, 8388608]
    ![8388609, 11003449, 11002462, 8906259, 8388736, 8445968, 57456, 57584, 8415040, 8389968,
    8389632, 11601278, 8893156, 2115580, 2114715, 8390470, 6471477, 11805554, 7338855, 6020157,
    8388842, 3145872, 14107252, 8388784]
    ![8388609, 11003449, 2580537, 8906357, 459605, 25110, 8413814, 483620, 484596, 8881381,
    34407, 11601176, 962610, 8748930, 8748261, 623652, 11222356, 10459150, 5063032, 10182463,
    4653627, 8290595, 7502346, 8388784] hf hy hc (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_line_products
    monsterCo1GeometryVectorPoint12Transport monsterCo1GeometryVectorPoint73Transport 5
    monsterCo1GeometryVectorPoint12Matrix monsterCo1GeometryVectorPoint12InverseMatrix
    monsterCo1GeometryVectorPoint73Matrix
    monsterCo1GeometryVectorPoint116AfterSignMatrix
    monsterCo1GeometryVectorPoint116AfterInverseMatrix monsterCo1GeometryVectorPoint116Matrix
    monsterCo1GeometryVectorPoint12Transport_binary
    monsterCo1GeometryVectorPoint12Transport_inverse_binary
    monsterCo1GeometryVectorPoint73Transport_binary
    hc1 hc2 hc3 v

/-- Source point 116 is the literal actual transported frame point. -/
def monsterCo1GeometryVectorPoint116 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryVectorPoint116Transport • monsterCo1GeometryBasePoint

/-- Complete binary coordinates of this literal actual source point. -/
theorem monsterCo1GeometryVectorPoint116_binary :
    monsterCo1GeometryVectorPoint116.val =
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0] := by
  change co1BinaryAction monsterCo1GeometryVectorPoint116Transport monsterCo1GeometryBasePoint.val =
      _
  rw [monsterCo1GeometryVectorPoint116Transport_binary, monsterCo1GeometryBasePoint_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
