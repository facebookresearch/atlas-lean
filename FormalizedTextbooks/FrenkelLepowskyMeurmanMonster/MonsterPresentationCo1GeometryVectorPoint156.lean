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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint077
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint153

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The literal actual two-core word for source point 156. -/
def monsterCo1GeometryVectorPoint156Transport : Co1 :=
  monsterCo1GeometryVectorPoint77Transport * monsterCo1GeometryTransportOperator 1 *
    monsterCo1GeometryVectorPoint77Transport⁻¹ * monsterCo1GeometryVectorPoint153Transport

/-- Complete displayed binary matrix of actual transport 156. -/
def monsterCo1GeometryVectorPoint156Matrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![11592951, 992248, 12, 11593482, 11584870, 9421940, 8397296, 4137859, 12576350, 4187486,
      1041033, 7532745, 10681568, 8839512, 8605957, 4994464, 378413, 1912342, 4981211,
      13766435, 13098336, 16661758, 15779491, 8388848]

/-- First complete finite matrix product in literal actual transport 156. -/
def monsterCo1GeometryVectorPoint156AfterSignMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![8447105, 2028246, 9353089, 10385153, 16, 8447152, 8445968, 1040, 24784, 26272, 8389632,
      2361307, 976582, 9437393, 8413398, 1081350, 5713703, 2228304, 2266041, 13809743,
      10502828, 10518656, 11196691, 8389840]

/-- Second complete finite matrix product in literal actual transport 156. -/
def monsterCo1GeometryVectorPoint156AfterInverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![145, 8389490, 1156, 8389608, 16, 1056, 1088, 128, 256, 512, 1024, 44042, 5136, 8397808,
      16384, 8422240, 79811, 172170, 303130, 579378, 1090714, 2139290, 12993425, 8388608]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 24000000 in
-- Check every entry of this finite actual transport matrix in the Lean kernel.
/-- Every column of transport 156 is its actual Conway binary action. -/
theorem monsterCo1GeometryVectorPoint156Transport_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint156Transport v =
      monsterCo1GeometryVectorPoint156Matrix *ᵥ v := by
  have hx : monsterCo1GeometryVectorPoint77Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![8446081, 10417350, 964497, 1996049, 16, 57520, 58384, 1040, 24784, 26272, 8389632,
    10749659, 9364182, 1049297, 8413398, 9471494, 5716247, 2228544, 2266793, 5417567, 2115500,
    2131328, 2803725, 8389840] := by rfl
  have hxi : monsterCo1GeometryVectorPoint77InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![57424, 3600533, 3585285, 423625, 16, 58609, 8445969, 58369, 41114, 8390496, 144,
    12597261, 8443090, 8396957, 9629, 8390080, 10471575, 2228544, 9447591, 11696967, 49968,
    10502603, 15526728, 1168] := by rfl
  have hy : monsterCo1GeometryVectorPoint153Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![4129298, 11534570, 3195142, 8397565, 11584870, 8398589, 9421689, 4137859, 12576350,
    4187486, 1041033, 524874, 1956623, 451017, 8605957, 4445140, 11468640, 5709215, 9032887,
    21509, 3328262, 731288, 1948041, 8388848] := by rfl
  have he : monsterCo1GeometryVectorPoint156AfterSignMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![8447105, 2028246, 9353089, 10385153, 16, 8447152, 8445968, 1040, 24784, 26272, 8389632,
    2361307, 976582, 9437393, 8413398, 1081350, 5713703, 2228304, 2266041, 13809743, 10502828,
    10518656, 11196691, 8389840] := by rfl
  have hf : monsterCo1GeometryVectorPoint156AfterInverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![145, 8389490, 1156, 8389608, 16, 1056, 1088, 128, 256, 512, 1024, 44042, 5136, 8397808,
    16384, 8422240, 79811, 172170, 303130, 579378, 1090714, 2139290, 12993425, 8388608] := by rfl
  have hc : monsterCo1GeometryVectorPoint156Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![11592951, 992248, 12, 11593482, 11584870, 9421940, 8397296, 4137859, 12576350, 4187486,
    1041033, 7532745, 10681568, 8839512, 8605957, 4994464, 378413, 1912342, 4981211, 13766435,
    13098336, 16661758, 15779491, 8388848] := by rfl
  have hc1 : monsterCo1GeometryVectorPoint77Matrix *
    monsterCo1GeometryTransportOperatorMatrix 1 =
    monsterCo1GeometryVectorPoint156AfterSignMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![8446081, 10417350, 964497, 1996049, 16, 57520, 58384, 1040, 24784, 26272, 8389632,
    10749659, 9364182, 1049297, 8413398, 9471494, 5716247, 2228544, 2266793, 5417567, 2115500,
    2131328, 2803725, 8389840]
      (monsterCo1GeometryBinaryOperatorMasks 1)
    ![8447105, 2028246, 9353089, 10385153, 16, 8447152, 8445968, 1040, 24784, 26272, 8389632,
    2361307, 976582, 9437393, 8413398, 1081350, 5713703, 2228304, 2266041, 13809743, 10502828,
    10518656, 11196691, 8389840] hx (monsterCo1GeometryBinaryOperatorMasks_decode 1) he (by
    decide +kernel)
  have hc2 : monsterCo1GeometryVectorPoint156AfterSignMatrix *
    monsterCo1GeometryVectorPoint77InverseMatrix =
    monsterCo1GeometryVectorPoint156AfterInverseMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![8447105, 2028246, 9353089, 10385153, 16, 8447152, 8445968, 1040, 24784, 26272, 8389632,
    2361307, 976582, 9437393, 8413398, 1081350, 5713703, 2228304, 2266041, 13809743, 10502828,
    10518656, 11196691, 8389840]
    ![57424, 3600533, 3585285, 423625, 16, 58609, 8445969, 58369, 41114, 8390496, 144,
    12597261, 8443090, 8396957, 9629, 8390080, 10471575, 2228544, 9447591, 11696967, 49968,
    10502603, 15526728, 1168]
    ![145, 8389490, 1156, 8389608, 16, 1056, 1088, 128, 256, 512, 1024, 44042, 5136, 8397808,
    16384, 8422240, 79811, 172170, 303130, 579378, 1090714, 2139290, 12993425, 8388608] he hxi
    hf (by decide +kernel)
  have hc3 : monsterCo1GeometryVectorPoint156AfterInverseMatrix *
    monsterCo1GeometryVectorPoint153Matrix = monsterCo1GeometryVectorPoint156Matrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![145, 8389490, 1156, 8389608, 16, 1056, 1088, 128, 256, 512, 1024, 44042, 5136, 8397808,
    16384, 8422240, 79811, 172170, 303130, 579378, 1090714, 2139290, 12993425, 8388608]
    ![4129298, 11534570, 3195142, 8397565, 11584870, 8398589, 9421689, 4137859, 12576350,
    4187486, 1041033, 524874, 1956623, 451017, 8605957, 4445140, 11468640, 5709215, 9032887,
    21509, 3328262, 731288, 1948041, 8388848]
    ![11592951, 992248, 12, 11593482, 11584870, 9421940, 8397296, 4137859, 12576350, 4187486,
    1041033, 7532745, 10681568, 8839512, 8605957, 4994464, 378413, 1912342, 4981211, 13766435,
    13098336, 16661758, 15779491, 8388848] hf hy hc (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_line_products
    monsterCo1GeometryVectorPoint77Transport monsterCo1GeometryVectorPoint153Transport 1
    monsterCo1GeometryVectorPoint77Matrix monsterCo1GeometryVectorPoint77InverseMatrix
    monsterCo1GeometryVectorPoint153Matrix
    monsterCo1GeometryVectorPoint156AfterSignMatrix
    monsterCo1GeometryVectorPoint156AfterInverseMatrix monsterCo1GeometryVectorPoint156Matrix
    monsterCo1GeometryVectorPoint77Transport_binary
    monsterCo1GeometryVectorPoint77Transport_inverse_binary
    monsterCo1GeometryVectorPoint153Transport_binary
    hc1 hc2 hc3 v

/-- Source point 156 is the literal actual transported frame point. -/
def monsterCo1GeometryVectorPoint156 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryVectorPoint156Transport • monsterCo1GeometryBasePoint

/-- Complete binary coordinates of this literal actual source point. -/
theorem monsterCo1GeometryVectorPoint156_binary :
    monsterCo1GeometryVectorPoint156.val =
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 1, 1, 0, 0] := by
  change co1BinaryAction monsterCo1GeometryVectorPoint156Transport monsterCo1GeometryBasePoint.val =
      _
  rw [monsterCo1GeometryVectorPoint156Transport_binary, monsterCo1GeometryBasePoint_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
