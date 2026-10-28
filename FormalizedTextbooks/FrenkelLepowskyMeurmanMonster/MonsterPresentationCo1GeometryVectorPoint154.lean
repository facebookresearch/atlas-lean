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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint153

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The literal actual two-core word for source point 154. -/
def monsterCo1GeometryVectorPoint154Transport : Co1 :=
  monsterCo1GeometryVectorPoint5Transport * monsterCo1GeometryTransportOperator 5 *
    monsterCo1GeometryVectorPoint5Transport⁻¹ * monsterCo1GeometryVectorPoint153Transport

/-- Complete displayed binary matrix of actual transport 154. -/
def monsterCo1GeometryVectorPoint154Matrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![11585126, 12575234, 3195142, 8390493, 4129042, 8398589, 9421689, 11591930, 4178114,
      12567759, 1041033, 8913270, 6417940, 16446030, 7381098, 12842312, 2169949, 14029475,
      159522, 1021609, 13555816, 723164, 1881481, 8388848]

/-- First complete finite matrix product in literal actual transport 154. -/
def monsterCo1GeometryVectorPoint154AfterSignMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![57584, 53856, 8450752, 45904, 57488, 8388736, 8388640, 8446016, 8438192, 50112, 8388768,
      4227936, 8763140, 1066422, 9462203, 8438876, 3417877, 6707933, 16300404, 2172724,
      11535533, 2098257, 14633659, 8389632]

/-- Second complete finite matrix product in literal actual transport 154. -/
def monsterCo1GeometryVectorPoint154AfterInverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![1057, 2034, 4, 271, 1072, 32, 64, 192, 720, 1456, 1024, 2775, 8426224, 8429856, 8439504,
      33744, 11609293, 2306243, 10232253, 12067709, 2138314, 9446541, 6369812, 8388608]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 24000000 in
-- Check every entry of this finite actual transport matrix in the Lean kernel.
/-- Every column of transport 154 is its actual Conway binary action. -/
theorem monsterCo1GeometryVectorPoint154Transport_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint154Transport v =
      monsterCo1GeometryVectorPoint154Matrix *ᵥ v := by
  have hx : monsterCo1GeometryVectorPoint5Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![57552, 8442048, 8450752, 45744, 57520, 8388736, 8388640, 57440, 49968, 49472, 8388768,
    12615680, 373992, 1066202, 1073783, 50908, 3418111, 15161819, 16366555, 2172254, 11535595,
    10486939, 14568157, 8389632] := by decide +kernel
  have hxi : monsterCo1GeometryVectorPoint5InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![57441, 643285, 3765294, 12185673, 225, 1056, 1073, 1088, 1366, 1008, 8389728, 13004640,
    1908, 1014, 1180, 2043, 1152766, 6127893, 2651647, 4454267, 3145968, 1098844, 2971, 1120]
    := by decide +kernel
  have hy : monsterCo1GeometryVectorPoint153Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![4129298, 11534570, 3195142, 8397565, 11584870, 8398589, 9421689, 4137859, 12576350,
    4187486, 1041033, 524874, 1956623, 451017, 8605957, 4445140, 11468640, 5709215, 9032887,
    21509, 3328262, 731288, 1948041, 8388848] := by rfl
  have he : monsterCo1GeometryVectorPoint154AfterSignMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![57584, 53856, 8450752, 45904, 57488, 8388736, 8388640, 8446016, 8438192, 50112, 8388768,
    4227936, 8763140, 1066422, 9462203, 8438876, 3417877, 6707933, 16300404, 2172724, 11535533,
    2098257, 14633659, 8389632] := by rfl
  have hf : monsterCo1GeometryVectorPoint154AfterInverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![1057, 2034, 4, 271, 1072, 32, 64, 192, 720, 1456, 1024, 2775, 8426224, 8429856, 8439504,
    33744, 11609293, 2306243, 10232253, 12067709, 2138314, 9446541, 6369812, 8388608] := by rfl
  have hc : monsterCo1GeometryVectorPoint154Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![11585126, 12575234, 3195142, 8390493, 4129042, 8398589, 9421689, 11591930, 4178114,
    12567759, 1041033, 8913270, 6417940, 16446030, 7381098, 12842312, 2169949, 14029475,
    159522, 1021609, 13555816, 723164, 1881481, 8388848] := by rfl
  have hc1 : monsterCo1GeometryVectorPoint5Matrix * monsterCo1GeometryTransportOperatorMatrix
    5 = monsterCo1GeometryVectorPoint154AfterSignMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![57552, 8442048, 8450752, 45744, 57520, 8388736, 8388640, 57440, 49968, 49472, 8388768,
    12615680, 373992, 1066202, 1073783, 50908, 3418111, 15161819, 16366555, 2172254, 11535595,
    10486939, 14568157, 8389632]
      (monsterCo1GeometryBinaryOperatorMasks 5)
    ![57584, 53856, 8450752, 45904, 57488, 8388736, 8388640, 8446016, 8438192, 50112, 8388768,
    4227936, 8763140, 1066422, 9462203, 8438876, 3417877, 6707933, 16300404, 2172724, 11535533,
    2098257, 14633659, 8389632] hx (monsterCo1GeometryBinaryOperatorMasks_decode 5) he (by
    decide +kernel)
  have hc2 : monsterCo1GeometryVectorPoint154AfterSignMatrix *
    monsterCo1GeometryVectorPoint5InverseMatrix =
    monsterCo1GeometryVectorPoint154AfterInverseMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![57584, 53856, 8450752, 45904, 57488, 8388736, 8388640, 8446016, 8438192, 50112, 8388768,
    4227936, 8763140, 1066422, 9462203, 8438876, 3417877, 6707933, 16300404, 2172724, 11535533,
    2098257, 14633659, 8389632]
    ![57441, 643285, 3765294, 12185673, 225, 1056, 1073, 1088, 1366, 1008, 8389728, 13004640,
    1908, 1014, 1180, 2043, 1152766, 6127893, 2651647, 4454267, 3145968, 1098844, 2971, 1120]
    ![1057, 2034, 4, 271, 1072, 32, 64, 192, 720, 1456, 1024, 2775, 8426224, 8429856, 8439504,
    33744, 11609293, 2306243, 10232253, 12067709, 2138314, 9446541, 6369812, 8388608] he hxi hf
    (by decide +kernel)
  have hc3 : monsterCo1GeometryVectorPoint154AfterInverseMatrix *
    monsterCo1GeometryVectorPoint153Matrix = monsterCo1GeometryVectorPoint154Matrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![1057, 2034, 4, 271, 1072, 32, 64, 192, 720, 1456, 1024, 2775, 8426224, 8429856, 8439504,
    33744, 11609293, 2306243, 10232253, 12067709, 2138314, 9446541, 6369812, 8388608]
    ![4129298, 11534570, 3195142, 8397565, 11584870, 8398589, 9421689, 4137859, 12576350,
    4187486, 1041033, 524874, 1956623, 451017, 8605957, 4445140, 11468640, 5709215, 9032887,
    21509, 3328262, 731288, 1948041, 8388848]
    ![11585126, 12575234, 3195142, 8390493, 4129042, 8398589, 9421689, 11591930, 4178114,
    12567759, 1041033, 8913270, 6417940, 16446030, 7381098, 12842312, 2169949, 14029475,
    159522, 1021609, 13555816, 723164, 1881481, 8388848] hf hy hc (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_line_products
    monsterCo1GeometryVectorPoint5Transport monsterCo1GeometryVectorPoint153Transport 5
    monsterCo1GeometryVectorPoint5Matrix monsterCo1GeometryVectorPoint5InverseMatrix
    monsterCo1GeometryVectorPoint153Matrix
    monsterCo1GeometryVectorPoint154AfterSignMatrix
    monsterCo1GeometryVectorPoint154AfterInverseMatrix monsterCo1GeometryVectorPoint154Matrix
    monsterCo1GeometryVectorPoint5Transport_binary
    monsterCo1GeometryVectorPoint5Transport_inverse_binary
    monsterCo1GeometryVectorPoint153Transport_binary
    hc1 hc2 hc3 v

/-- Source point 154 is the literal actual transported frame point. -/
def monsterCo1GeometryVectorPoint154 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryVectorPoint154Transport • monsterCo1GeometryBasePoint

/-- Complete binary coordinates of this literal actual source point. -/
theorem monsterCo1GeometryVectorPoint154_binary :
    monsterCo1GeometryVectorPoint154.val =
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 1, 1, 0, 0] := by
  change co1BinaryAction monsterCo1GeometryVectorPoint154Transport monsterCo1GeometryBasePoint.val =
      _
  rw [monsterCo1GeometryVectorPoint154Transport_binary, monsterCo1GeometryBasePoint_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
