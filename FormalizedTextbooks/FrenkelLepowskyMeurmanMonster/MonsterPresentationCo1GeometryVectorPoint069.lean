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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint032

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The literal actual two-core word for source point 69. -/
def monsterCo1GeometryVectorPoint69Transport : Co1 :=
  monsterCo1GeometryVectorPoint15Transport * monsterCo1GeometryTransportOperator 1 *
    monsterCo1GeometryVectorPoint15Transport⁻¹ * monsterCo1GeometryVectorPoint32Transport

/-- Complete displayed binary matrix of actual transport 69. -/
def monsterCo1GeometryVectorPoint69Matrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  ![![0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 1],
    ![0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
    ![1, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1],
    ![0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1],
    ![1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1],
    ![0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 1, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1],
    ![1, 1, 1, 1, 0, 0, 0, 1, 0, 0, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1],
    ![0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1],
    ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1],
    ![0, 1, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 1, 1],
    ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 1, 0],
    ![0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1],
    ![1, 1, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0],
    ![1, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 1, 0],
    ![0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1],
    ![1, 0, 1, 0, 0, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1],
    ![0, 1, 1, 0, 0, 1, 1, 1, 0, 1, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0],
    ![0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 0, 0, 1, 1, 1, 1, 1, 0],
    ![0, 1, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1],
    ![1, 0, 1, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1],
    ![1, 1, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1]]

/-- First complete finite matrix product in literal actual transport 69. -/
def monsterCo1GeometryVectorPoint69AfterSignMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  ![![0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 1, 0, 1],
    ![0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1],
    ![1, 1, 1, 1, 0, 0, 1, 0, 0, 0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1],
    ![0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1],
    ![1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0],
    ![0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1],
    ![1, 1, 1, 1, 0, 0, 0, 1, 0, 0, 1, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0],
    ![0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 1, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1],
    ![1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1],
    ![0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 0, 1, 1],
    ![0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 0, 1, 0],
    ![1, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 0, 0, 0, 1],
    ![1, 1, 0, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 1],
    ![0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0],
    ![0, 1, 0, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1],
    ![0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 1, 1],
    ![1, 1, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 0, 1],
    ![0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0],
    ![0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1],
    ![1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1]]

/-- Second complete finite matrix product in literal actual transport 69. -/
def monsterCo1GeometryVectorPoint69AfterInverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1],
    ![1, 0, 0, 1, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1],
    ![1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0],
    ![0, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 1],
    ![1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0],
    ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 1],
    ![1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0],
    ![0, 0, 1, 1, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0],
    ![0, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 0, 1],
    ![1, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0],
    ![1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1],
    ![1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1],
    ![1, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 1, 1, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0],
    ![0, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 0, 0, 0, 1, 1, 1, 0, 0, 0, 1, 0, 0, 1],
    ![0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 1, 1, 1, 0],
    ![1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 1],
    ![1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0],
    ![1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 1, 1],
    ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]]

set_option maxHeartbeats 24000000 in
-- Check every entry of this finite actual transport matrix in the Lean kernel.
/-- Every column of transport 69 is its actual Conway binary action. -/
theorem monsterCo1GeometryVectorPoint69Transport_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint69Transport v =
      monsterCo1GeometryVectorPoint69Matrix *ᵥ v := by
  have hx : monsterCo1GeometryVectorPoint15Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![49312, 8421584, 11560912, 10511824, 12601423, 12627006, 12610767, 12610590, 12635279,
    12635182, 9438720, 5683319, 6180408, 12970498, 355693, 380765, 8646666, 1593978, 5389864,
    12384167, 9523772, 6568274, 338093, 58368] := by decide +kernel
  have hxi : monsterCo1GeometryVectorPoint15InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![8389616, 9359062, 4053439, 11679898, 1310, 8388689, 8390287, 161, 12599777, 49792,
    12517955, 8380818, 9766028, 12518066, 12518796, 4130173, 9102121, 10622437, 8774188,
    1373312, 49804, 4211179, 8308941, 12518991] := by decide +kernel
  have hy : monsterCo1GeometryVectorPoint32Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![49312, 8421584, 34768, 8421840, 8433728, 8409136, 8417472, 8425488, 8441984, 8400928,
    8446464, 2428173, 9363974, 1435148, 6680077, 7669773, 12807268, 13159669, 12766456,
    13413529, 4299954, 4504803, 4574125, 8389632] := by decide +kernel
  have he : monsterCo1GeometryVectorPoint69AfterSignMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![49312, 34000, 11560144, 10511568, 12606543, 12631102, 4226255, 12614686, 4250767,
    12639278, 9438208, 14068327, 14571560, 4587042, 8748355, 8773491, 259130, 9983098,
    13772856, 12382375, 1135644, 14953554, 343171, 8445952] := by decide +kernel
  have hf : monsterCo1GeometryVectorPoint69AfterInverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![1, 1038, 12616549, 12599785, 2754271, 9766060, 2753155, 9765900, 2753475, 9766540, 50816,
    2805085, 9819934, 1384657, 11234657, 11251041, 8454467, 181900, 9553694, 7831842, 9488093,
    7684449, 15411565, 8389644] := by decide +kernel
  have hc : monsterCo1GeometryVectorPoint69Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![49312, 8414416, 11550848, 2097328, 12589135, 12590094, 12598479, 12639278, 12622991,
    12614686, 9479216, 16057122, 6162456, 13978130, 5661495, 4621623, 12814420, 14184133,
    1189606, 8163320, 13712034, 10786237, 7774871, 8445952] := by decide +kernel
  have hc1 : monsterCo1GeometryVectorPoint15Matrix *
    monsterCo1GeometryTransportOperatorMatrix 1 =
    monsterCo1GeometryVectorPoint69AfterSignMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![49312, 8421584, 11560912, 10511824, 12601423, 12627006, 12610767, 12610590, 12635279,
    12635182, 9438720, 5683319, 6180408, 12970498, 355693, 380765, 8646666, 1593978, 5389864,
    12384167, 9523772, 6568274, 338093, 58368]
      (monsterCo1GeometryBinaryOperatorMasks 1)
    ![49312, 34000, 11560144, 10511568, 12606543, 12631102, 4226255, 12614686, 4250767,
    12639278, 9438208, 14068327, 14571560, 4587042, 8748355, 8773491, 259130, 9983098,
    13772856, 12382375, 1135644, 14953554, 343171, 8445952] hx
    (monsterCo1GeometryBinaryOperatorMasks_decode 1) he (by decide +kernel)
  have hc2 : monsterCo1GeometryVectorPoint69AfterSignMatrix *
    monsterCo1GeometryVectorPoint15InverseMatrix =
    monsterCo1GeometryVectorPoint69AfterInverseMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![49312, 34000, 11560144, 10511568, 12606543, 12631102, 4226255, 12614686, 4250767,
    12639278, 9438208, 14068327, 14571560, 4587042, 8748355, 8773491, 259130, 9983098,
    13772856, 12382375, 1135644, 14953554, 343171, 8445952]
    ![8389616, 9359062, 4053439, 11679898, 1310, 8388689, 8390287, 161, 12599777, 49792,
    12517955, 8380818, 9766028, 12518066, 12518796, 4130173, 9102121, 10622437, 8774188,
    1373312, 49804, 4211179, 8308941, 12518991]
    ![1, 1038, 12616549, 12599785, 2754271, 9766060, 2753155, 9765900, 2753475, 9766540, 50816,
    2805085, 9819934, 1384657, 11234657, 11251041, 8454467, 181900, 9553694, 7831842, 9488093,
    7684449, 15411565, 8389644] he hxi hf (by decide +kernel)
  have hc3 : monsterCo1GeometryVectorPoint69AfterInverseMatrix *
    monsterCo1GeometryVectorPoint32Matrix = monsterCo1GeometryVectorPoint69Matrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![1, 1038, 12616549, 12599785, 2754271, 9766060, 2753155, 9765900, 2753475, 9766540, 50816,
    2805085, 9819934, 1384657, 11234657, 11251041, 8454467, 181900, 9553694, 7831842, 9488093,
    7684449, 15411565, 8389644]
    ![49312, 8421584, 34768, 8421840, 8433728, 8409136, 8417472, 8425488, 8441984, 8400928,
    8446464, 2428173, 9363974, 1435148, 6680077, 7669773, 12807268, 13159669, 12766456,
    13413529, 4299954, 4504803, 4574125, 8389632]
    ![49312, 8414416, 11550848, 2097328, 12589135, 12590094, 12598479, 12639278, 12622991,
    12614686, 9479216, 16057122, 6162456, 13978130, 5661495, 4621623, 12814420, 14184133,
    1189606, 8163320, 13712034, 10786237, 7774871, 8445952] hf hy hc (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_line_products
    monsterCo1GeometryVectorPoint15Transport monsterCo1GeometryVectorPoint32Transport 1
    monsterCo1GeometryVectorPoint15Matrix monsterCo1GeometryVectorPoint15InverseMatrix
    monsterCo1GeometryVectorPoint32Matrix
    monsterCo1GeometryVectorPoint69AfterSignMatrix
    monsterCo1GeometryVectorPoint69AfterInverseMatrix monsterCo1GeometryVectorPoint69Matrix
    monsterCo1GeometryVectorPoint15Transport_binary
    monsterCo1GeometryVectorPoint15Transport_inverse_binary
    monsterCo1GeometryVectorPoint32Transport_binary
    hc1 hc2 hc3 v

/-- Source point 69 is the literal actual transported frame point. -/
def monsterCo1GeometryVectorPoint69 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryVectorPoint69Transport • monsterCo1GeometryBasePoint

/-- Complete binary coordinates of this literal actual source point. -/
theorem monsterCo1GeometryVectorPoint69_binary :
    monsterCo1GeometryVectorPoint69.val =
      ![0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0] := by
  change co1BinaryAction monsterCo1GeometryVectorPoint69Transport monsterCo1GeometryBasePoint.val =
      _
  rw [monsterCo1GeometryVectorPoint69Transport_binary, monsterCo1GeometryBasePoint_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
