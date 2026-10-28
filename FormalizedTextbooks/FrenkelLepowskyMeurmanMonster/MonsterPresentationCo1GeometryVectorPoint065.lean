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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint014
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint030

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The literal actual two-core word for source point 65. -/
def monsterCo1GeometryVectorPoint65Transport : Co1 :=
  monsterCo1GeometryVectorPoint14Transport * monsterCo1GeometryTransportOperator 5 *
    monsterCo1GeometryVectorPoint14Transport⁻¹ * monsterCo1GeometryVectorPoint30Transport

/-- Complete displayed binary matrix of actual transport 65. -/
def monsterCo1GeometryVectorPoint65Matrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  ![![0, 0, 0, 1, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1],
    ![0, 0, 0, 1, 0, 1, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 0, 1],
    ![0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 0],
    ![0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 0, 1, 1, 1, 0, 0, 1, 0, 1],
    ![0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 1, 0, 1],
    ![0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 0, 0],
    ![0, 1, 1, 0, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 0, 1],
    ![0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 1, 0, 1],
    ![1, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 0],
    ![1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 0],
    ![0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1],
    ![1, 0, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 0, 0, 1, 0, 0, 0, 1, 1, 0, 1],
    ![1, 1, 0, 1, 1, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 1, 0, 1, 1, 1, 0],
    ![0, 0, 1, 0, 0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 1],
    ![0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0],
    ![1, 0, 1, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 1, 1, 0, 0, 1, 1, 0],
    ![0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 1, 1, 0, 1],
    ![1, 0, 1, 1, 0, 0, 0, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 1, 0, 0, 1, 1, 0],
    ![0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
    ![0, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 1, 0, 1, 0],
    ![0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0],
    ![0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0],
    ![0, 0, 1, 1, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0],
    ![0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

/-- First complete finite matrix product in literal actual transport 65. -/
def monsterCo1GeometryVectorPoint65AfterSignMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  ![![1, 1, 0, 0, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1],
    ![1, 1, 0, 0, 1, 0, 0, 1, 1, 1, 1, 0, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0],
    ![0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 0, 0],
    ![0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 1, 1, 1, 0, 1, 0, 1, 0, 0, 0],
    ![1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0],
    ![1, 1, 0, 0, 0, 0, 1, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0],
    ![1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1],
    ![1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1],
    ![0, 0, 0, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0],
    ![0, 0, 1, 0, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0],
    ![1, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0],
    ![0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1],
    ![1, 1, 1, 1, 0, 0, 1, 1, 0, 1, 1, 1, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0],
    ![1, 1, 1, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 1],
    ![1, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1],
    ![1, 1, 1, 0, 1, 0, 1, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 1],
    ![1, 1, 0, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 1],
    ![0, 1, 1, 1, 0, 1, 0, 0, 1, 1, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 1, 1, 0],
    ![1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0],
    ![1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 1, 0, 1],
    ![1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 1, 1, 1, 1, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]]

/-- Second complete finite matrix product in literal actual transport 65. -/
def monsterCo1GeometryVectorPoint65AfterInverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  ![![0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1],
    ![1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1],
    ![0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 0],
    ![0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 0],
    ![0, 1, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 0],
    ![0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 0],
    ![1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1],
    ![1, 1, 1, 0, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1],
    ![1, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 0],
    ![1, 0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 0],
    ![1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1],
    ![1, 0, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0],
    ![0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0],
    ![1, 0, 0, 0, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 0, 1, 0, 0, 1, 1, 1, 1, 0],
    ![1, 0, 0, 0, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 0, 0, 0, 1, 1, 0, 1, 1, 1, 0],
    ![1, 0, 1, 1, 0, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 1],
    ![1, 0, 1, 1, 0, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 1],
    ![1, 0, 1, 1, 1, 1, 0, 0, 1, 0, 0, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 1, 0],
    ![1, 0, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 0],
    ![0, 1, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1],
    ![0, 1, 1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1],
    ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 1],
    ![0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]]

set_option maxHeartbeats 24000000 in
-- Check every entry of this finite actual transport matrix in the Lean kernel.
/-- Every column of transport 65 is its actual Conway binary action. -/
theorem monsterCo1GeometryVectorPoint65Transport_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint65Transport v =
      monsterCo1GeometryVectorPoint65Matrix *ᵥ v := by
  have hx : monsterCo1GeometryVectorPoint14Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![4129584, 11155152, 9819692, 9823788, 12572128, 12575904, 12575824, 12572368, 12598711,
    12598907, 12518640, 8338236, 212047, 196611, 11780878, 11584461, 5285275, 5330007, 6460587,
    6317671, 3966339, 3950147, 260096, 50176] := by decide +kernel
  have hxi : monsterCo1GeometryVectorPoint14InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![12149857, 11969681, 1035948, 1035612, 13620263, 13579335, 13619968, 13579008, 13620028,
    13579212, 11534576, 8380428, 3146747, 3146743, 9486509, 10535005, 16527408, 15978688,
    7152297, 5972312, 9507100, 11072140, 8383473, 11535361] := by decide +kernel
  have hy : monsterCo1GeometryVectorPoint30Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![8388800, 8451008, 61632, 29600, 57520, 32, 8388640, 57440, 49968, 49472, 8388768,
    12615680, 8738040, 1075162, 9461879, 1996, 3212038, 15161819, 6904285, 11600565, 3203078,
    11591776, 3946495, 8389632] := by decide +kernel
  have he : monsterCo1GeometryVectorPoint65AfterSignMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![12518003, 2766739, 1431052, 1434764, 4183555, 4187587, 12576051, 12571955, 4276024,
    4275444, 4130227, 16660720, 147151, 196620, 11780551, 11583755, 13673687, 13718811,
    6461230, 6317549, 12355503, 12338927, 194560, 50816] := by decide +kernel
  have hf : monsterCo1GeometryVectorPoint65AfterInverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![12567756, 12567759, 8335426, 8335490, 7401558, 7401642, 12645579, 12645575, 4454141,
    4453885, 12566733, 4996913, 16523516, 1041152, 7944945, 7748081, 11601869, 11667405,
    8223037, 8305213, 10485882, 9437366, 12333104, 8388812] := by decide +kernel
  have hc : monsterCo1GeometryVectorPoint65Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![10355176, 10416872, 2619118, 10950318, 12157072, 3736352, 12125990, 12158022, 7306027,
    7305563, 10355080, 11615541, 7638171, 9307044, 6898776, 6768541, 11626064, 6765709,
    1055906, 5645236, 3179696, 3205110, 5082300, 26400] := by decide +kernel
  have hc1 : monsterCo1GeometryVectorPoint14Matrix *
    monsterCo1GeometryTransportOperatorMatrix 5 =
    monsterCo1GeometryVectorPoint65AfterSignMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![4129584, 11155152, 9819692, 9823788, 12572128, 12575904, 12575824, 12572368, 12598711,
    12598907, 12518640, 8338236, 212047, 196611, 11780878, 11584461, 5285275, 5330007, 6460587,
    6317671, 3966339, 3950147, 260096, 50176]
      (monsterCo1GeometryBinaryOperatorMasks 5)
    ![12518003, 2766739, 1431052, 1434764, 4183555, 4187587, 12576051, 12571955, 4276024,
    4275444, 4130227, 16660720, 147151, 196620, 11780551, 11583755, 13673687, 13718811,
    6461230, 6317549, 12355503, 12338927, 194560, 50816] hx
    (monsterCo1GeometryBinaryOperatorMasks_decode 5) he (by decide +kernel)
  have hc2 : monsterCo1GeometryVectorPoint65AfterSignMatrix *
    monsterCo1GeometryVectorPoint14InverseMatrix =
    monsterCo1GeometryVectorPoint65AfterInverseMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![12518003, 2766739, 1431052, 1434764, 4183555, 4187587, 12576051, 12571955, 4276024,
    4275444, 4130227, 16660720, 147151, 196620, 11780551, 11583755, 13673687, 13718811,
    6461230, 6317549, 12355503, 12338927, 194560, 50816]
    ![12149857, 11969681, 1035948, 1035612, 13620263, 13579335, 13619968, 13579008, 13620028,
    13579212, 11534576, 8380428, 3146747, 3146743, 9486509, 10535005, 16527408, 15978688,
    7152297, 5972312, 9507100, 11072140, 8383473, 11535361]
    ![12567756, 12567759, 8335426, 8335490, 7401558, 7401642, 12645579, 12645575, 4454141,
    4453885, 12566733, 4996913, 16523516, 1041152, 7944945, 7748081, 11601869, 11667405,
    8223037, 8305213, 10485882, 9437366, 12333104, 8388812] he hxi hf (by decide +kernel)
  have hc3 : monsterCo1GeometryVectorPoint65AfterInverseMatrix *
    monsterCo1GeometryVectorPoint30Matrix = monsterCo1GeometryVectorPoint65Matrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![12567756, 12567759, 8335426, 8335490, 7401558, 7401642, 12645579, 12645575, 4454141,
    4453885, 12566733, 4996913, 16523516, 1041152, 7944945, 7748081, 11601869, 11667405,
    8223037, 8305213, 10485882, 9437366, 12333104, 8388812]
    ![8388800, 8451008, 61632, 29600, 57520, 32, 8388640, 57440, 49968, 49472, 8388768,
    12615680, 8738040, 1075162, 9461879, 1996, 3212038, 15161819, 6904285, 11600565, 3203078,
    11591776, 3946495, 8389632]
    ![10355176, 10416872, 2619118, 10950318, 12157072, 3736352, 12125990, 12158022, 7306027,
    7305563, 10355080, 11615541, 7638171, 9307044, 6898776, 6768541, 11626064, 6765709,
    1055906, 5645236, 3179696, 3205110, 5082300, 26400] hf hy hc (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_line_products
    monsterCo1GeometryVectorPoint14Transport monsterCo1GeometryVectorPoint30Transport 5
    monsterCo1GeometryVectorPoint14Matrix monsterCo1GeometryVectorPoint14InverseMatrix
    monsterCo1GeometryVectorPoint30Matrix
    monsterCo1GeometryVectorPoint65AfterSignMatrix
    monsterCo1GeometryVectorPoint65AfterInverseMatrix monsterCo1GeometryVectorPoint65Matrix
    monsterCo1GeometryVectorPoint14Transport_binary
    monsterCo1GeometryVectorPoint14Transport_inverse_binary
    monsterCo1GeometryVectorPoint30Transport_binary
    hc1 hc2 hc3 v

/-- Source point 65 is the literal actual transported frame point. -/
def monsterCo1GeometryVectorPoint65 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryVectorPoint65Transport • monsterCo1GeometryBasePoint

/-- Complete binary coordinates of this literal actual source point. -/
theorem monsterCo1GeometryVectorPoint65_binary :
    monsterCo1GeometryVectorPoint65.val =
      ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0] := by
  change co1BinaryAction monsterCo1GeometryVectorPoint65Transport monsterCo1GeometryBasePoint.val =
      _
  rw [monsterCo1GeometryVectorPoint65Transport_binary, monsterCo1GeometryBasePoint_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
