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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint015
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint081

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The literal actual two-core word for source point 127. -/
def monsterCo1GeometryVectorPoint127Transport : Co1 :=
  monsterCo1GeometryVectorPoint15Transport * monsterCo1GeometryTransportOperator 6 *
    monsterCo1GeometryVectorPoint15Transport⁻¹ * monsterCo1GeometryVectorPoint81Transport

/-- Complete displayed binary matrix of actual transport 127. -/
def monsterCo1GeometryVectorPoint127Matrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![3291117, 12611, 1292073, 5150, 10713103, 10733935, 9567938, 9567810, 2358812, 10746248,
      9675143, 222053, 10754264, 15948173, 5447392, 6363693, 1219807, 5667175, 16770101,
      14376503, 15873578, 9624356, 13839523, 45972]

/-- First complete finite matrix product in literal actual transport 127. -/
def monsterCo1GeometryVectorPoint127AfterSignMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![8438240, 33280, 11560346, 10512220, 4344784, 4370353, 12742144, 12742353, 12766656,
      4377953, 9438918, 5552164, 6049639, 4712728, 8875175, 511255, 8646661, 9982000, 13647777,
      3994923, 1134965, 6699867, 469751, 8446992]

/-- Second complete finite matrix product in literal actual transport 127. -/
def monsterCo1GeometryVectorPoint127AfterInverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![16728352, 4179965, 12333639, 9380620, 6076775, 6077513, 10747144, 10747336, 6520712,
      14449351, 3347783, 2937682, 6515606, 14762905, 6414889, 2008998, 8399875, 78860,
      15427968, 3679563, 14530763, 11594767, 6169272, 4129617]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 24000000 in
-- Check every entry of this finite actual transport matrix in the Lean kernel.
/-- Every column of transport 127 is its actual Conway binary action. -/
theorem monsterCo1GeometryVectorPoint127Transport_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint127Transport v =
      monsterCo1GeometryVectorPoint127Matrix *ᵥ v := by
  have hx : monsterCo1GeometryVectorPoint15Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![49312, 8421584, 11560912, 10511824, 12601423, 12627006, 12610767, 12610590, 12635279,
    12635182, 9438720, 5683319, 6180408, 12970498, 355693, 380765, 8646666, 1593978, 5389864,
    12384167, 9523772, 6568274, 338093, 58368] := by decide +kernel
  have hxi : monsterCo1GeometryVectorPoint15InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![8389616, 9359062, 4053439, 11679898, 1310, 8388689, 8390287, 161, 12599777, 49792,
    12517955, 8380818, 9766028, 12518066, 12518796, 4130173, 9102121, 10622437, 8774188,
    1373312, 49804, 4211179, 8308941, 12518991] := by decide +kernel
  have hy : monsterCo1GeometryVectorPoint81Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![1040, 13648, 4864, 4352, 57504, 58400, 57456, 57584, 8413856, 8415040, 8388784, 9620777,
    471428, 8414214, 10495244, 2138555, 5320277, 12967738, 13622218, 5986653, 1091053, 1074337,
    9577173, 8389632] := by rfl
  have he : monsterCo1GeometryVectorPoint127AfterSignMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![8438240, 33280, 11560346, 10512220, 4344784, 4370353, 12742144, 12742353, 12766656,
    4377953, 9438918, 5552164, 6049639, 4712728, 8875175, 511255, 8646661, 9982000, 13647777,
    3994923, 1134965, 6699867, 469751, 8446992] := by rfl
  have hf : monsterCo1GeometryVectorPoint127AfterInverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![16728352, 4179965, 12333639, 9380620, 6076775, 6077513, 10747144, 10747336, 6520712,
    14449351, 3347783, 2937682, 6515606, 14762905, 6414889, 2008998, 8399875, 78860, 15427968,
    3679563, 14530763, 11594767, 6169272, 4129617] := by rfl
  have hc : monsterCo1GeometryVectorPoint127Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![3291117, 12611, 1292073, 5150, 10713103, 10733935, 9567938, 9567810, 2358812, 10746248,
    9675143, 222053, 10754264, 15948173, 5447392, 6363693, 1219807, 5667175, 16770101,
    14376503, 15873578, 9624356, 13839523, 45972] := by rfl
  have hc1 : monsterCo1GeometryVectorPoint15Matrix *
    monsterCo1GeometryTransportOperatorMatrix 6 =
    monsterCo1GeometryVectorPoint127AfterSignMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![49312, 8421584, 11560912, 10511824, 12601423, 12627006, 12610767, 12610590, 12635279,
    12635182, 9438720, 5683319, 6180408, 12970498, 355693, 380765, 8646666, 1593978, 5389864,
    12384167, 9523772, 6568274, 338093, 58368]
      (monsterCo1GeometryBinaryOperatorMasks 6)
    ![8438240, 33280, 11560346, 10512220, 4344784, 4370353, 12742144, 12742353, 12766656,
    4377953, 9438918, 5552164, 6049639, 4712728, 8875175, 511255, 8646661, 9982000, 13647777,
    3994923, 1134965, 6699867, 469751, 8446992] hx
    (monsterCo1GeometryBinaryOperatorMasks_decode 6) he (by decide +kernel)
  have hc2 : monsterCo1GeometryVectorPoint127AfterSignMatrix *
    monsterCo1GeometryVectorPoint15InverseMatrix =
    monsterCo1GeometryVectorPoint127AfterInverseMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![8438240, 33280, 11560346, 10512220, 4344784, 4370353, 12742144, 12742353, 12766656,
    4377953, 9438918, 5552164, 6049639, 4712728, 8875175, 511255, 8646661, 9982000, 13647777,
    3994923, 1134965, 6699867, 469751, 8446992]
    ![8389616, 9359062, 4053439, 11679898, 1310, 8388689, 8390287, 161, 12599777, 49792,
    12517955, 8380818, 9766028, 12518066, 12518796, 4130173, 9102121, 10622437, 8774188,
    1373312, 49804, 4211179, 8308941, 12518991]
    ![16728352, 4179965, 12333639, 9380620, 6076775, 6077513, 10747144, 10747336, 6520712,
    14449351, 3347783, 2937682, 6515606, 14762905, 6414889, 2008998, 8399875, 78860, 15427968,
    3679563, 14530763, 11594767, 6169272, 4129617] he hxi hf (by decide +kernel)
  have hc3 : monsterCo1GeometryVectorPoint127AfterInverseMatrix *
    monsterCo1GeometryVectorPoint81Matrix = monsterCo1GeometryVectorPoint127Matrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![16728352, 4179965, 12333639, 9380620, 6076775, 6077513, 10747144, 10747336, 6520712,
    14449351, 3347783, 2937682, 6515606, 14762905, 6414889, 2008998, 8399875, 78860, 15427968,
    3679563, 14530763, 11594767, 6169272, 4129617]
    ![1040, 13648, 4864, 4352, 57504, 58400, 57456, 57584, 8413856, 8415040, 8388784, 9620777,
    471428, 8414214, 10495244, 2138555, 5320277, 12967738, 13622218, 5986653, 1091053, 1074337,
    9577173, 8389632]
    ![3291117, 12611, 1292073, 5150, 10713103, 10733935, 9567938, 9567810, 2358812, 10746248,
    9675143, 222053, 10754264, 15948173, 5447392, 6363693, 1219807, 5667175, 16770101,
    14376503, 15873578, 9624356, 13839523, 45972] hf hy hc (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_line_products
    monsterCo1GeometryVectorPoint15Transport monsterCo1GeometryVectorPoint81Transport 6
    monsterCo1GeometryVectorPoint15Matrix monsterCo1GeometryVectorPoint15InverseMatrix
    monsterCo1GeometryVectorPoint81Matrix
    monsterCo1GeometryVectorPoint127AfterSignMatrix
    monsterCo1GeometryVectorPoint127AfterInverseMatrix monsterCo1GeometryVectorPoint127Matrix
    monsterCo1GeometryVectorPoint15Transport_binary
    monsterCo1GeometryVectorPoint15Transport_inverse_binary
    monsterCo1GeometryVectorPoint81Transport_binary
    hc1 hc2 hc3 v

/-- Source point 127 is the literal actual transported frame point. -/
def monsterCo1GeometryVectorPoint127 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryVectorPoint127Transport • monsterCo1GeometryBasePoint

/-- Complete binary coordinates of this literal actual source point. -/
theorem monsterCo1GeometryVectorPoint127_binary :
    monsterCo1GeometryVectorPoint127.val =
      ![0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 0] := by
  change co1BinaryAction monsterCo1GeometryVectorPoint127Transport monsterCo1GeometryBasePoint.val =
      _
  rw [monsterCo1GeometryVectorPoint127Transport_binary, monsterCo1GeometryBasePoint_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
