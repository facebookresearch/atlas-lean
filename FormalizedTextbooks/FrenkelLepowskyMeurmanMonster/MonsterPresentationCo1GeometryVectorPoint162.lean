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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint147
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint154

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The literal actual two-core word for source point 162. -/
def monsterCo1GeometryVectorPoint162Transport : Co1 :=
  monsterCo1GeometryVectorPoint147Transport * monsterCo1GeometryTransportOperator 1 *
    monsterCo1GeometryVectorPoint147Transport⁻¹ * monsterCo1GeometryVectorPoint154Transport

/-- Complete displayed binary matrix of actual transport 162. -/
def monsterCo1GeometryVectorPoint162Matrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![12575235, 3195142, 12575234, 3146534, 11543271, 9372265, 3203943, 3204970, 4177971,
      58577, 11584151, 14107333, 4862057, 6776920, 874961, 75817, 5603682, 2877516, 15542506,
      9718959, 6054623, 14962452, 14575848, 8388848]

/-- First complete finite matrix product in literal actual transport 162. -/
def monsterCo1GeometryVectorPoint162AfterSignMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![8901748, 513237, 8901861, 10527211, 2593720, 2593609, 10948985, 10503164, 10503547,
      2560751, 2585561, 12113247, 10135684, 1523182, 276682, 13027718, 694948, 4586637,
      9462234, 4071113, 15824943, 1073344, 13027428, 1200]

/-- Second complete finite matrix product in literal actual transport 162. -/
def monsterCo1GeometryVectorPoint162AfterInverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![1464, 4, 2, 8390260, 8390397, 8389490, 8389509, 8389588, 8390635, 8389061, 8390597,
      8359932, 7668020, 1197368, 15573249, 9506946, 9146403, 9670675, 16482688, 16586568,
      16650951, 14647680, 13734018, 8388608]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 24000000 in
-- Check every entry of this finite actual transport matrix in the Lean kernel.
/-- Every column of transport 162 is its actual Conway binary action. -/
theorem monsterCo1GeometryVectorPoint162Transport_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint162Transport v =
      monsterCo1GeometryVectorPoint162Matrix *ᵥ v := by
  have hx : monsterCo1GeometryVectorPoint147Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![8901700, 8901861, 513237, 2138347, 10983048, 2594425, 2560073, 2115324, 10502267,
    10949599, 10973929, 3724895, 10140314, 9907152, 8662212, 13031830, 9080506, 4581549,
    9462746, 12455383, 7432975, 1073856, 13031540, 1200] := by rfl
  have hxi : monsterCo1GeometryVectorPoint147InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![15168521, 4227943, 14186344, 8647737, 6779170, 6780059, 6780078, 8388753, 8389571,
    16744832, 1320, 7419103, 16179616, 11567577, 11040172, 16744817, 12209371, 5942320,
    16709318, 6941439, 2097610, 15401811, 9140372, 1471] := by rfl
  have hy : monsterCo1GeometryVectorPoint154Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![11585126, 12575234, 3195142, 8390493, 4129042, 8398589, 9421689, 11591930, 4178114,
    12567759, 1041033, 8913270, 6417940, 16446030, 7381098, 12842312, 2169949, 14029475,
    159522, 1021609, 13555816, 723164, 1881481, 8388848] := by rfl
  have he : monsterCo1GeometryVectorPoint162AfterSignMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![8901748, 513237, 8901861, 10527211, 2593720, 2593609, 10948985, 10503164, 10503547,
    2560751, 2585561, 12113247, 10135684, 1523182, 276682, 13027718, 694948, 4586637, 9462234,
    4071113, 15824943, 1073344, 13027428, 1200] := by rfl
  have hf : monsterCo1GeometryVectorPoint162AfterInverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![1464, 4, 2, 8390260, 8390397, 8389490, 8389509, 8389588, 8390635, 8389061, 8390597,
    8359932, 7668020, 1197368, 15573249, 9506946, 9146403, 9670675, 16482688, 16586568,
    16650951, 14647680, 13734018, 8388608] := by rfl
  have hc : monsterCo1GeometryVectorPoint162Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![12575235, 3195142, 12575234, 3146534, 11543271, 9372265, 3203943, 3204970, 4177971,
    58577, 11584151, 14107333, 4862057, 6776920, 874961, 75817, 5603682, 2877516, 15542506,
    9718959, 6054623, 14962452, 14575848, 8388848] := by rfl
  have hc1 : monsterCo1GeometryVectorPoint147Matrix *
    monsterCo1GeometryTransportOperatorMatrix 1 =
    monsterCo1GeometryVectorPoint162AfterSignMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![8901700, 8901861, 513237, 2138347, 10983048, 2594425, 2560073, 2115324, 10502267,
    10949599, 10973929, 3724895, 10140314, 9907152, 8662212, 13031830, 9080506, 4581549,
    9462746, 12455383, 7432975, 1073856, 13031540, 1200]
      (monsterCo1GeometryBinaryOperatorMasks 1)
    ![8901748, 513237, 8901861, 10527211, 2593720, 2593609, 10948985, 10503164, 10503547,
    2560751, 2585561, 12113247, 10135684, 1523182, 276682, 13027718, 694948, 4586637, 9462234,
    4071113, 15824943, 1073344, 13027428, 1200] hx
    (monsterCo1GeometryBinaryOperatorMasks_decode 1) he (by decide +kernel)
  have hc2 : monsterCo1GeometryVectorPoint162AfterSignMatrix *
    monsterCo1GeometryVectorPoint147InverseMatrix =
    monsterCo1GeometryVectorPoint162AfterInverseMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![8901748, 513237, 8901861, 10527211, 2593720, 2593609, 10948985, 10503164, 10503547,
    2560751, 2585561, 12113247, 10135684, 1523182, 276682, 13027718, 694948, 4586637, 9462234,
    4071113, 15824943, 1073344, 13027428, 1200]
    ![15168521, 4227943, 14186344, 8647737, 6779170, 6780059, 6780078, 8388753, 8389571,
    16744832, 1320, 7419103, 16179616, 11567577, 11040172, 16744817, 12209371, 5942320,
    16709318, 6941439, 2097610, 15401811, 9140372, 1471]
    ![1464, 4, 2, 8390260, 8390397, 8389490, 8389509, 8389588, 8390635, 8389061, 8390597,
    8359932, 7668020, 1197368, 15573249, 9506946, 9146403, 9670675, 16482688, 16586568,
    16650951, 14647680, 13734018, 8388608] he hxi hf (by decide +kernel)
  have hc3 : monsterCo1GeometryVectorPoint162AfterInverseMatrix *
    monsterCo1GeometryVectorPoint154Matrix = monsterCo1GeometryVectorPoint162Matrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![1464, 4, 2, 8390260, 8390397, 8389490, 8389509, 8389588, 8390635, 8389061, 8390597,
    8359932, 7668020, 1197368, 15573249, 9506946, 9146403, 9670675, 16482688, 16586568,
    16650951, 14647680, 13734018, 8388608]
    ![11585126, 12575234, 3195142, 8390493, 4129042, 8398589, 9421689, 11591930, 4178114,
    12567759, 1041033, 8913270, 6417940, 16446030, 7381098, 12842312, 2169949, 14029475,
    159522, 1021609, 13555816, 723164, 1881481, 8388848]
    ![12575235, 3195142, 12575234, 3146534, 11543271, 9372265, 3203943, 3204970, 4177971,
    58577, 11584151, 14107333, 4862057, 6776920, 874961, 75817, 5603682, 2877516, 15542506,
    9718959, 6054623, 14962452, 14575848, 8388848] hf hy hc (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_line_products
    monsterCo1GeometryVectorPoint147Transport monsterCo1GeometryVectorPoint154Transport 1
    monsterCo1GeometryVectorPoint147Matrix monsterCo1GeometryVectorPoint147InverseMatrix
    monsterCo1GeometryVectorPoint154Matrix
    monsterCo1GeometryVectorPoint162AfterSignMatrix
    monsterCo1GeometryVectorPoint162AfterInverseMatrix monsterCo1GeometryVectorPoint162Matrix
    monsterCo1GeometryVectorPoint147Transport_binary
    monsterCo1GeometryVectorPoint147Transport_inverse_binary
    monsterCo1GeometryVectorPoint154Transport_binary
    hc1 hc2 hc3 v

/-- Source point 162 is the literal actual transported frame point. -/
def monsterCo1GeometryVectorPoint162 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryVectorPoint162Transport • monsterCo1GeometryBasePoint

/-- Complete binary coordinates of this literal actual source point. -/
theorem monsterCo1GeometryVectorPoint162_binary :
    monsterCo1GeometryVectorPoint162.val =
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0] := by
  change co1BinaryAction monsterCo1GeometryVectorPoint162Transport monsterCo1GeometryBasePoint.val =
      _
  rw [monsterCo1GeometryVectorPoint162Transport_binary, monsterCo1GeometryBasePoint_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
