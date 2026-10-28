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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint162

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The literal actual two-core word for source point 169. -/
def monsterCo1GeometryVectorPoint169Transport : Co1 :=
  monsterCo1GeometryVectorPoint12Transport * monsterCo1GeometryTransportOperator 5 *
    monsterCo1GeometryVectorPoint12Transport⁻¹ * monsterCo1GeometryVectorPoint162Transport

/-- Complete displayed binary matrix of actual transport 169. -/
def monsterCo1GeometryVectorPoint169Matrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![12575235, 3195142, 8389616, 11534518, 8390400, 11591830, 983448, 12525807, 1042137,
      9379929, 9380709, 5718357, 8599183, 9064825, 14704880, 4713644, 16348202, 8392718,
      12580431, 12689152, 423528, 16293670, 3363273, 8388848]

/-- First complete finite matrix product in literal actual transport 169. -/
def monsterCo1GeometryVectorPoint169AfterSignMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![128, 8450752, 53856, 8446144, 37280, 49232, 49392, 21408, 29264, 45808, 8192, 4198432,
      9430880, 4537389, 4536448, 329261, 10495201, 7531209, 6548037, 11543649, 10794169,
      11826325, 13694990, 8389632]

/-- Second complete finite matrix product in literal actual transport 169. -/
def monsterCo1GeometryVectorPoint169AfterInverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![1, 2, 2034, 1039, 1615, 1975, 2007, 1326, 1854, 1999, 1014, 3079, 10982336, 16770032,
      16745456, 3768560, 5654126, 5916062, 6637215, 6702447, 8275111, 7816279, 12567536,
      8388608]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 24000000 in
-- Check every entry of this finite actual transport matrix in the Lean kernel.
/-- Every column of transport 169 is its actual Conway binary action. -/
theorem monsterCo1GeometryVectorPoint169Transport_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint169Transport v =
      monsterCo1GeometryVectorPoint169Matrix *ᵥ v := by
  have hx : monsterCo1GeometryVectorPoint12Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![128, 8450752, 8442048, 57568, 37600, 8438480, 8438384, 21088, 28976, 45840, 8397472,
    12587008, 1041989, 4471982, 4470787, 328737, 2107019, 15985327, 14871215, 3155591,
    10794911, 11826623, 13760653, 8389632] := by decide +kernel
  have hxi : monsterCo1GeometryVectorPoint12InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![12150534, 7383031, 2025057, 2614625, 1065, 97, 783, 1, 1696, 1008, 8389734, 13004640,
    2045, 1014, 2019, 1906, 3539712, 6128234, 1040385, 4454386, 3146496, 7283185, 2971, 1126]
    := by decide +kernel
  have hy : monsterCo1GeometryVectorPoint162Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![12575235, 3195142, 12575234, 3146534, 11543271, 9372265, 3203943, 3204970, 4177971,
    58577, 11584151, 14107333, 4862057, 6776920, 874961, 75817, 5603682, 2877516, 15542506,
    9718959, 6054623, 14962452, 14575848, 8388848] := by rfl
  have he : monsterCo1GeometryVectorPoint169AfterSignMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![128, 8450752, 53856, 8446144, 37280, 49232, 49392, 21408, 29264, 45808, 8192, 4198432,
    9430880, 4537389, 4536448, 329261, 10495201, 7531209, 6548037, 11543649, 10794169,
    11826325, 13694990, 8389632] := by rfl
  have hf : monsterCo1GeometryVectorPoint169AfterInverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![1, 2, 2034, 1039, 1615, 1975, 2007, 1326, 1854, 1999, 1014, 3079, 10982336, 16770032,
    16745456, 3768560, 5654126, 5916062, 6637215, 6702447, 8275111, 7816279, 12567536, 8388608]
    := by rfl
  have hc : monsterCo1GeometryVectorPoint169Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![12575235, 3195142, 8389616, 11534518, 8390400, 11591830, 983448, 12525807, 1042137,
    9379929, 9380709, 5718357, 8599183, 9064825, 14704880, 4713644, 16348202, 8392718,
    12580431, 12689152, 423528, 16293670, 3363273, 8388848] := by rfl
  have hc1 : monsterCo1GeometryVectorPoint12Matrix *
    monsterCo1GeometryTransportOperatorMatrix 5 =
    monsterCo1GeometryVectorPoint169AfterSignMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![128, 8450752, 8442048, 57568, 37600, 8438480, 8438384, 21088, 28976, 45840, 8397472,
    12587008, 1041989, 4471982, 4470787, 328737, 2107019, 15985327, 14871215, 3155591,
    10794911, 11826623, 13760653, 8389632]
      (monsterCo1GeometryBinaryOperatorMasks 5)
    ![128, 8450752, 53856, 8446144, 37280, 49232, 49392, 21408, 29264, 45808, 8192, 4198432,
    9430880, 4537389, 4536448, 329261, 10495201, 7531209, 6548037, 11543649, 10794169,
    11826325, 13694990, 8389632] hx (monsterCo1GeometryBinaryOperatorMasks_decode 5) he (by
    decide +kernel)
  have hc2 : monsterCo1GeometryVectorPoint169AfterSignMatrix *
    monsterCo1GeometryVectorPoint12InverseMatrix =
    monsterCo1GeometryVectorPoint169AfterInverseMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![128, 8450752, 53856, 8446144, 37280, 49232, 49392, 21408, 29264, 45808, 8192, 4198432,
    9430880, 4537389, 4536448, 329261, 10495201, 7531209, 6548037, 11543649, 10794169,
    11826325, 13694990, 8389632]
    ![12150534, 7383031, 2025057, 2614625, 1065, 97, 783, 1, 1696, 1008, 8389734, 13004640,
    2045, 1014, 2019, 1906, 3539712, 6128234, 1040385, 4454386, 3146496, 7283185, 2971, 1126]
    ![1, 2, 2034, 1039, 1615, 1975, 2007, 1326, 1854, 1999, 1014, 3079, 10982336, 16770032,
    16745456, 3768560, 5654126, 5916062, 6637215, 6702447, 8275111, 7816279, 12567536, 8388608]
    he hxi hf (by decide +kernel)
  have hc3 : monsterCo1GeometryVectorPoint169AfterInverseMatrix *
    monsterCo1GeometryVectorPoint162Matrix = monsterCo1GeometryVectorPoint169Matrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![1, 2, 2034, 1039, 1615, 1975, 2007, 1326, 1854, 1999, 1014, 3079, 10982336, 16770032,
    16745456, 3768560, 5654126, 5916062, 6637215, 6702447, 8275111, 7816279, 12567536, 8388608]
    ![12575235, 3195142, 12575234, 3146534, 11543271, 9372265, 3203943, 3204970, 4177971,
    58577, 11584151, 14107333, 4862057, 6776920, 874961, 75817, 5603682, 2877516, 15542506,
    9718959, 6054623, 14962452, 14575848, 8388848]
    ![12575235, 3195142, 8389616, 11534518, 8390400, 11591830, 983448, 12525807, 1042137,
    9379929, 9380709, 5718357, 8599183, 9064825, 14704880, 4713644, 16348202, 8392718,
    12580431, 12689152, 423528, 16293670, 3363273, 8388848] hf hy hc (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_line_products
    monsterCo1GeometryVectorPoint12Transport monsterCo1GeometryVectorPoint162Transport 5
    monsterCo1GeometryVectorPoint12Matrix monsterCo1GeometryVectorPoint12InverseMatrix
    monsterCo1GeometryVectorPoint162Matrix
    monsterCo1GeometryVectorPoint169AfterSignMatrix
    monsterCo1GeometryVectorPoint169AfterInverseMatrix monsterCo1GeometryVectorPoint169Matrix
    monsterCo1GeometryVectorPoint12Transport_binary
    monsterCo1GeometryVectorPoint12Transport_inverse_binary
    monsterCo1GeometryVectorPoint162Transport_binary
    hc1 hc2 hc3 v

/-- Source point 169 is the literal actual transported frame point. -/
def monsterCo1GeometryVectorPoint169 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryVectorPoint169Transport • monsterCo1GeometryBasePoint

/-- Complete binary coordinates of this literal actual source point. -/
theorem monsterCo1GeometryVectorPoint169_binary :
    monsterCo1GeometryVectorPoint169.val =
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0] := by
  change co1BinaryAction monsterCo1GeometryVectorPoint169Transport monsterCo1GeometryBasePoint.val =
      _
  rw [monsterCo1GeometryVectorPoint169Transport_binary, monsterCo1GeometryBasePoint_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
