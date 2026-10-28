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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint047
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint154

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The literal actual two-core word for source point 158. -/
def monsterCo1GeometryVectorPoint158Transport : Co1 :=
  monsterCo1GeometryVectorPoint47Transport * monsterCo1GeometryTransportOperator 1 *
    monsterCo1GeometryVectorPoint47Transport⁻¹ * monsterCo1GeometryVectorPoint154Transport

/-- Complete displayed binary matrix of actual transport 158. -/
def monsterCo1GeometryVectorPoint158Matrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![11585126, 50896, 5285592, 6033812, 14510654, 14829874, 13798535, 13799221, 6459196,
      14527232, 11768734, 6895775, 54046, 10993070, 16695936, 5085090, 1981298, 13977446,
      6509096, 15725972, 5081424, 677128, 3011505, 4138018]

/-- First complete finite matrix product in literal actual transport 158. -/
def monsterCo1GeometryVectorPoint158AfterSignMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![49312, 34000, 3179728, 2131152, 12606543, 4217918, 4226255, 4234270, 4250767, 4209710,
      9438208, 14056663, 6215912, 12967586, 5613004, 5572604, 8646666, 9983098, 13814824,
      12382375, 9523260, 14953554, 5627916, 8445952]

/-- Second complete finite matrix product in literal actual transport 158. -/
def monsterCo1GeometryVectorPoint158AfterInverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![1, 1038, 12616549, 12599785, 2754271, 9766060, 2753155, 9765900, 2753475, 9766540, 50816,
      2805085, 9819934, 1384657, 11234657, 11251041, 8454467, 181900, 9553694, 7831842,
      9488093, 7684449, 15411565, 8389644]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 24000000 in
-- Check every entry of this finite actual transport matrix in the Lean kernel.
/-- Every column of transport 158 is its actual Conway binary action. -/
theorem monsterCo1GeometryVectorPoint158Transport_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint158Transport v =
      monsterCo1GeometryVectorPoint158Matrix *ᵥ v := by
  have hx : monsterCo1GeometryVectorPoint47Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![49312, 8421584, 11568080, 10518992, 12601423, 12601406, 12610767, 12617758, 12635279,
    12593198, 9438720, 5664455, 6212344, 12963458, 5613538, 5572050, 259130, 1593978, 13819448,
    12384167, 1136156, 6568274, 14018082, 58368] := by decide +kernel
  have hxi : monsterCo1GeometryVectorPoint47InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![1008, 10751636, 9903603, 1637591, 1310, 8388689, 8390287, 161, 12600813, 49792, 12518991,
    8381634, 9764992, 12519102, 12517760, 4129137, 713593, 2233589, 8774189, 9760911, 49804,
    12600807, 13897182, 12517955] := by decide +kernel
  have hy : monsterCo1GeometryVectorPoint154Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![11585126, 12575234, 3195142, 8390493, 4129042, 8398589, 9421689, 11591930, 4178114,
    12567759, 1041033, 8913270, 6417940, 16446030, 7381098, 12842312, 2169949, 14029475,
    159522, 1021609, 13555816, 723164, 1881481, 8388848] := by rfl
  have he : monsterCo1GeometryVectorPoint158AfterSignMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![49312, 34000, 3179728, 2131152, 12606543, 4217918, 4226255, 4234270, 4250767, 4209710,
    9438208, 14056663, 6215912, 12967586, 5613004, 5572604, 8646666, 9983098, 13814824,
    12382375, 9523260, 14953554, 5627916, 8445952] := by rfl
  have hf : monsterCo1GeometryVectorPoint158AfterInverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![1, 1038, 12616549, 12599785, 2754271, 9766060, 2753155, 9765900, 2753475, 9766540, 50816,
    2805085, 9819934, 1384657, 11234657, 11251041, 8454467, 181900, 9553694, 7831842, 9488093,
    7684449, 15411565, 8389644] := by rfl
  have hc : monsterCo1GeometryVectorPoint158Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![11585126, 50896, 5285592, 6033812, 14510654, 14829874, 13798535, 13799221, 6459196,
    14527232, 11768734, 6895775, 54046, 10993070, 16695936, 5085090, 1981298, 13977446,
    6509096, 15725972, 5081424, 677128, 3011505, 4138018] := by rfl
  have hc1 : monsterCo1GeometryVectorPoint47Matrix *
    monsterCo1GeometryTransportOperatorMatrix 1 =
    monsterCo1GeometryVectorPoint158AfterSignMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![49312, 8421584, 11568080, 10518992, 12601423, 12601406, 12610767, 12617758, 12635279,
    12593198, 9438720, 5664455, 6212344, 12963458, 5613538, 5572050, 259130, 1593978, 13819448,
    12384167, 1136156, 6568274, 14018082, 58368]
      (monsterCo1GeometryBinaryOperatorMasks 1)
    ![49312, 34000, 3179728, 2131152, 12606543, 4217918, 4226255, 4234270, 4250767, 4209710,
    9438208, 14056663, 6215912, 12967586, 5613004, 5572604, 8646666, 9983098, 13814824,
    12382375, 9523260, 14953554, 5627916, 8445952] hx
    (monsterCo1GeometryBinaryOperatorMasks_decode 1) he (by decide +kernel)
  have hc2 : monsterCo1GeometryVectorPoint158AfterSignMatrix *
    monsterCo1GeometryVectorPoint47InverseMatrix =
    monsterCo1GeometryVectorPoint158AfterInverseMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![49312, 34000, 3179728, 2131152, 12606543, 4217918, 4226255, 4234270, 4250767, 4209710,
    9438208, 14056663, 6215912, 12967586, 5613004, 5572604, 8646666, 9983098, 13814824,
    12382375, 9523260, 14953554, 5627916, 8445952]
    ![1008, 10751636, 9903603, 1637591, 1310, 8388689, 8390287, 161, 12600813, 49792, 12518991,
    8381634, 9764992, 12519102, 12517760, 4129137, 713593, 2233589, 8774189, 9760911, 49804,
    12600807, 13897182, 12517955]
    ![1, 1038, 12616549, 12599785, 2754271, 9766060, 2753155, 9765900, 2753475, 9766540, 50816,
    2805085, 9819934, 1384657, 11234657, 11251041, 8454467, 181900, 9553694, 7831842, 9488093,
    7684449, 15411565, 8389644] he hxi hf (by decide +kernel)
  have hc3 : monsterCo1GeometryVectorPoint158AfterInverseMatrix *
    monsterCo1GeometryVectorPoint154Matrix = monsterCo1GeometryVectorPoint158Matrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![1, 1038, 12616549, 12599785, 2754271, 9766060, 2753155, 9765900, 2753475, 9766540, 50816,
    2805085, 9819934, 1384657, 11234657, 11251041, 8454467, 181900, 9553694, 7831842, 9488093,
    7684449, 15411565, 8389644]
    ![11585126, 12575234, 3195142, 8390493, 4129042, 8398589, 9421689, 11591930, 4178114,
    12567759, 1041033, 8913270, 6417940, 16446030, 7381098, 12842312, 2169949, 14029475,
    159522, 1021609, 13555816, 723164, 1881481, 8388848]
    ![11585126, 50896, 5285592, 6033812, 14510654, 14829874, 13798535, 13799221, 6459196,
    14527232, 11768734, 6895775, 54046, 10993070, 16695936, 5085090, 1981298, 13977446,
    6509096, 15725972, 5081424, 677128, 3011505, 4138018] hf hy hc (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_line_products
    monsterCo1GeometryVectorPoint47Transport monsterCo1GeometryVectorPoint154Transport 1
    monsterCo1GeometryVectorPoint47Matrix monsterCo1GeometryVectorPoint47InverseMatrix
    monsterCo1GeometryVectorPoint154Matrix
    monsterCo1GeometryVectorPoint158AfterSignMatrix
    monsterCo1GeometryVectorPoint158AfterInverseMatrix monsterCo1GeometryVectorPoint158Matrix
    monsterCo1GeometryVectorPoint47Transport_binary
    monsterCo1GeometryVectorPoint47Transport_inverse_binary
    monsterCo1GeometryVectorPoint154Transport_binary
    hc1 hc2 hc3 v

/-- Source point 158 is the literal actual transported frame point. -/
def monsterCo1GeometryVectorPoint158 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryVectorPoint158Transport • monsterCo1GeometryBasePoint

/-- Complete binary coordinates of this literal actual source point. -/
theorem monsterCo1GeometryVectorPoint158_binary :
    monsterCo1GeometryVectorPoint158.val =
      ![0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0] := by
  change co1BinaryAction monsterCo1GeometryVectorPoint158Transport monsterCo1GeometryBasePoint.val =
      _
  rw [monsterCo1GeometryVectorPoint158Transport_binary, monsterCo1GeometryBasePoint_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
