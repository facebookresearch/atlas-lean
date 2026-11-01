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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint064
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint160

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The literal actual two-core word for source point 167. -/
def monsterCo1GeometryVectorPoint167Transport : Co1 :=
  monsterCo1GeometryVectorPoint64Transport * monsterCo1GeometryTransportOperator 7 *
    monsterCo1GeometryVectorPoint64Transport⁻¹ * monsterCo1GeometryVectorPoint160Transport

/-- Complete displayed binary matrix of actual transport 167. -/
def monsterCo1GeometryVectorPoint167Matrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![9381832, 9380616, 8438384, 8390544, 1197, 11535286, 4138894, 8397216, 983560, 48,
      1041113, 7074757, 15726588, 4391923, 9409041, 14957174, 3170342, 4483902, 4943019,
      15207699, 14159387, 7685146, 1021320, 8388848]

/-- First complete finite matrix product in literal actual transport 167. -/
def monsterCo1GeometryVectorPoint167AfterSignMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![192, 8450880, 53520, 8388672, 8426192, 20480, 21408, 49696, 49792, 37744, 8784, 4255936,
      657125, 16711293, 16710256, 9373240, 3231941, 10589716, 2148007, 1201965, 1284023,
      3195402, 16710271, 8389632]

/-- Second complete finite matrix product in literal actual transport 167. -/
def monsterCo1GeometryVectorPoint167AfterInverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![1031, 1037, 1021, 1038, 1854, 241, 145, 889, 761, 1326, 1014, 3087, 10384176, 14782656,
      14807232, 12181744, 6242633, 8077961, 5916062, 5654126, 6898257, 5849505, 10596544,
      8388608]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 24000000 in
-- Check every entry of this finite actual transport matrix in the Lean kernel.
/-- Every column of transport 167 is its actual Conway binary action. -/
theorem monsterCo1GeometryVectorPoint167Transport_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint167Transport v =
      monsterCo1GeometryVectorPoint167Matrix *ᵥ v := by
  have hx : monsterCo1GeometryVectorPoint64Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![8388800, 8451008, 54064, 64, 8426336, 8410000, 8409136, 49152, 49312, 37568, 8432,
    4255808, 9045473, 16449005, 16447968, 9373488, 3232067, 2200990, 2147505, 9590683, 9672493,
    3194928, 16447983, 8389632] := by decide +kernel
  have hxi : monsterCo1GeometryVectorPoint64InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![10970550, 12592134, 10381014, 12150630, 312, 1423, 8, 1039, 1942, 1654, 8389638, 474511,
    1491, 1200, 1314, 1442, 4604648, 5588815, 14791703, 7484647, 222655, 2318728, 2539, 1030]
    := by decide +kernel
  have hy : monsterCo1GeometryVectorPoint160Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![9380969, 8388849, 9429285, 8389681, 4129042, 8398589, 983749, 9372405, 8541, 4130191,
    1041013, 6606908, 2320208, 8288992, 11725570, 13798757, 11560700, 4082267, 16469147,
    5778990, 10300013, 3171169, 3337371, 8388848] := by rfl
  have he : monsterCo1GeometryVectorPoint167AfterSignMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![192, 8450880, 53520, 8388672, 8426192, 20480, 21408, 49696, 49792, 37744, 8784, 4255936,
    657125, 16711293, 16710256, 9373240, 3231941, 10589716, 2148007, 1201965, 1284023, 3195402,
    16710271, 8389632] := by rfl
  have hf : monsterCo1GeometryVectorPoint167AfterInverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![1031, 1037, 1021, 1038, 1854, 241, 145, 889, 761, 1326, 1014, 3087, 10384176, 14782656,
    14807232, 12181744, 6242633, 8077961, 5916062, 5654126, 6898257, 5849505, 10596544,
    8388608] := by rfl
  have hc : monsterCo1GeometryVectorPoint167Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![9381832, 9380616, 8438384, 8390544, 1197, 11535286, 4138894, 8397216, 983560, 48,
    1041113, 7074757, 15726588, 4391923, 9409041, 14957174, 3170342, 4483902, 4943019,
    15207699, 14159387, 7685146, 1021320, 8388848] := by rfl
  have hc1 : monsterCo1GeometryVectorPoint64Matrix *
    monsterCo1GeometryTransportOperatorMatrix 7 =
    monsterCo1GeometryVectorPoint167AfterSignMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![8388800, 8451008, 54064, 64, 8426336, 8410000, 8409136, 49152, 49312, 37568, 8432,
    4255808, 9045473, 16449005, 16447968, 9373488, 3232067, 2200990, 2147505, 9590683, 9672493,
    3194928, 16447983, 8389632]
      (monsterCo1GeometryBinaryOperatorMasks 7)
    ![192, 8450880, 53520, 8388672, 8426192, 20480, 21408, 49696, 49792, 37744, 8784, 4255936,
    657125, 16711293, 16710256, 9373240, 3231941, 10589716, 2148007, 1201965, 1284023, 3195402,
    16710271, 8389632] hx (monsterCo1GeometryBinaryOperatorMasks_decode 7) he
      (by decide +kernel)
  have hc2 : monsterCo1GeometryVectorPoint167AfterSignMatrix *
    monsterCo1GeometryVectorPoint64InverseMatrix =
    monsterCo1GeometryVectorPoint167AfterInverseMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![192, 8450880, 53520, 8388672, 8426192, 20480, 21408, 49696, 49792, 37744, 8784, 4255936,
    657125, 16711293, 16710256, 9373240, 3231941, 10589716, 2148007, 1201965, 1284023, 3195402,
    16710271, 8389632]
    ![10970550, 12592134, 10381014, 12150630, 312, 1423, 8, 1039, 1942, 1654, 8389638, 474511,
    1491, 1200, 1314, 1442, 4604648, 5588815, 14791703, 7484647, 222655, 2318728, 2539, 1030]
    ![1031, 1037, 1021, 1038, 1854, 241, 145, 889, 761, 1326, 1014, 3087, 10384176, 14782656,
    14807232, 12181744, 6242633, 8077961, 5916062, 5654126, 6898257, 5849505, 10596544,
    8388608] he hxi hf (by decide +kernel)
  have hc3 : monsterCo1GeometryVectorPoint167AfterInverseMatrix *
    monsterCo1GeometryVectorPoint160Matrix = monsterCo1GeometryVectorPoint167Matrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![1031, 1037, 1021, 1038, 1854, 241, 145, 889, 761, 1326, 1014, 3087, 10384176, 14782656,
    14807232, 12181744, 6242633, 8077961, 5916062, 5654126, 6898257, 5849505, 10596544,
    8388608]
    ![9380969, 8388849, 9429285, 8389681, 4129042, 8398589, 983749, 9372405, 8541, 4130191,
    1041013, 6606908, 2320208, 8288992, 11725570, 13798757, 11560700, 4082267, 16469147,
    5778990, 10300013, 3171169, 3337371, 8388848]
    ![9381832, 9380616, 8438384, 8390544, 1197, 11535286, 4138894, 8397216, 983560, 48,
    1041113, 7074757, 15726588, 4391923, 9409041, 14957174, 3170342, 4483902, 4943019,
    15207699, 14159387, 7685146, 1021320, 8388848] hf hy hc (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_line_products
    monsterCo1GeometryVectorPoint64Transport monsterCo1GeometryVectorPoint160Transport 7
    monsterCo1GeometryVectorPoint64Matrix monsterCo1GeometryVectorPoint64InverseMatrix
    monsterCo1GeometryVectorPoint160Matrix
    monsterCo1GeometryVectorPoint167AfterSignMatrix
    monsterCo1GeometryVectorPoint167AfterInverseMatrix monsterCo1GeometryVectorPoint167Matrix
    monsterCo1GeometryVectorPoint64Transport_binary
    monsterCo1GeometryVectorPoint64Transport_inverse_binary
    monsterCo1GeometryVectorPoint160Transport_binary
    hc1 hc2 hc3 v

/-- Source point 167 is the literal actual transported frame point. -/
def monsterCo1GeometryVectorPoint167 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryVectorPoint167Transport • monsterCo1GeometryBasePoint

/-- Complete binary coordinates of this literal actual source point. -/
theorem monsterCo1GeometryVectorPoint167_binary :
    monsterCo1GeometryVectorPoint167.val =
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 1, 0, 0, 0] := by
  change co1BinaryAction monsterCo1GeometryVectorPoint167Transport monsterCo1GeometryBasePoint.val =
      _
  rw [monsterCo1GeometryVectorPoint167Transport_binary, monsterCo1GeometryBasePoint_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
