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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint041

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The literal actual two-core word for source point 90. -/
def monsterCo1GeometryVectorPoint90Transport : Co1 :=
  monsterCo1GeometryVectorPoint15Transport * monsterCo1GeometryTransportOperator 1 *
    monsterCo1GeometryVectorPoint15Transport⁻¹ * monsterCo1GeometryVectorPoint41Transport

/-- Complete displayed binary matrix of actual transport 90. -/
def monsterCo1GeometryVectorPoint90Matrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![49312, 34000, 8431488, 8390064, 8451136, 8450048, 54464, 8400928, 29824, 8425488,
      8405552, 12910604, 5176840, 14007346, 16185927, 15137351, 4455428, 14179381, 1179654,
      8181864, 9539612, 6556882, 5692135, 8389632]

/-- First complete finite matrix product in literal actual transport 90. -/
def monsterCo1GeometryVectorPoint90AfterSignMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![49312, 34000, 11560144, 10511568, 12606543, 12631102, 4226255, 12614686, 4250767,
      12639278, 9438208, 14068327, 14571560, 4587042, 8748355, 8773491, 259130, 9983098,
      13772856, 12382375, 1135644, 14953554, 343171, 8445952]

/-- Second complete finite matrix product in literal actual transport 90. -/
def monsterCo1GeometryVectorPoint90AfterInverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![1, 1038, 12616549, 12599785, 2754271, 9766060, 2753155, 9765900, 2753475, 9766540, 50816,
      2805085, 9819934, 1384657, 11234657, 11251041, 8454467, 181900, 9553694, 7831842,
      9488093, 7684449, 15411565, 8389644]

set_option maxHeartbeats 24000000 in
-- Check every entry of this finite actual transport matrix in the Lean kernel.
/-- Every column of transport 90 is its actual Conway binary action. -/
theorem monsterCo1GeometryVectorPoint90Transport_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint90Transport v =
      monsterCo1GeometryVectorPoint90Matrix *ᵥ v := by
  have hx : monsterCo1GeometryVectorPoint15Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![49312, 8421584, 11560912, 10511824, 12601423, 12627006, 12610767, 12610590, 12635279,
    12635182, 9438720, 5683319, 6180408, 12970498, 355693, 380765, 8646666, 1593978, 5389864,
    12384167, 9523772, 6568274, 338093, 58368] := by decide +kernel
  have hxi : monsterCo1GeometryVectorPoint15InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![8389616, 9359062, 4053439, 11679898, 1310, 8388689, 8390287, 161, 12599777, 49792,
    12517955, 8380818, 9766028, 12518066, 12518796, 4130173, 9102121, 10622437, 8774188,
    1373312, 49804, 4211179, 8308941, 12518991] := by decide +kernel
  have hy : monsterCo1GeometryVectorPoint41Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![49312, 8414416, 11568080, 10518992, 12627023, 12601406, 12610767, 12617758, 12635279,
    12593198, 9495040, 1440803, 10412566, 1376300, 15066146, 16114722, 12786740, 4725765,
    12721176, 4987913, 78860, 8704140, 12919938, 58368] := by decide +kernel
  have he : monsterCo1GeometryVectorPoint90AfterSignMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![49312, 34000, 11560144, 10511568, 12606543, 12631102, 4226255, 12614686, 4250767,
    12639278, 9438208, 14068327, 14571560, 4587042, 8748355, 8773491, 259130, 9983098,
    13772856, 12382375, 1135644, 14953554, 343171, 8445952] := by rfl
  have hf : monsterCo1GeometryVectorPoint90AfterInverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![1, 1038, 12616549, 12599785, 2754271, 9766060, 2753155, 9765900, 2753475, 9766540, 50816,
    2805085, 9819934, 1384657, 11234657, 11251041, 8454467, 181900, 9553694, 7831842, 9488093,
    7684449, 15411565, 8389644] := by rfl
  have hc : monsterCo1GeometryVectorPoint90Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![49312, 34000, 8431488, 8390064, 8451136, 8450048, 54464, 8400928, 29824, 8425488,
    8405552, 12910604, 5176840, 14007346, 16185927, 15137351, 4455428, 14179381, 1179654,
    8181864, 9539612, 6556882, 5692135, 8389632] := by rfl
  have hc1 : monsterCo1GeometryVectorPoint15Matrix *
    monsterCo1GeometryTransportOperatorMatrix 1 =
    monsterCo1GeometryVectorPoint90AfterSignMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![49312, 8421584, 11560912, 10511824, 12601423, 12627006, 12610767, 12610590, 12635279,
    12635182, 9438720, 5683319, 6180408, 12970498, 355693, 380765, 8646666, 1593978, 5389864,
    12384167, 9523772, 6568274, 338093, 58368]
      (monsterCo1GeometryBinaryOperatorMasks 1)
    ![49312, 34000, 11560144, 10511568, 12606543, 12631102, 4226255, 12614686, 4250767,
    12639278, 9438208, 14068327, 14571560, 4587042, 8748355, 8773491, 259130, 9983098,
    13772856, 12382375, 1135644, 14953554, 343171, 8445952] hx
    (monsterCo1GeometryBinaryOperatorMasks_decode 1) he (by decide +kernel)
  have hc2 : monsterCo1GeometryVectorPoint90AfterSignMatrix *
    monsterCo1GeometryVectorPoint15InverseMatrix =
    monsterCo1GeometryVectorPoint90AfterInverseMatrix :=
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
  have hc3 : monsterCo1GeometryVectorPoint90AfterInverseMatrix *
    monsterCo1GeometryVectorPoint41Matrix = monsterCo1GeometryVectorPoint90Matrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![1, 1038, 12616549, 12599785, 2754271, 9766060, 2753155, 9765900, 2753475, 9766540, 50816,
    2805085, 9819934, 1384657, 11234657, 11251041, 8454467, 181900, 9553694, 7831842, 9488093,
    7684449, 15411565, 8389644]
    ![49312, 8414416, 11568080, 10518992, 12627023, 12601406, 12610767, 12617758, 12635279,
    12593198, 9495040, 1440803, 10412566, 1376300, 15066146, 16114722, 12786740, 4725765,
    12721176, 4987913, 78860, 8704140, 12919938, 58368]
    ![49312, 34000, 8431488, 8390064, 8451136, 8450048, 54464, 8400928, 29824, 8425488,
    8405552, 12910604, 5176840, 14007346, 16185927, 15137351, 4455428, 14179381, 1179654,
    8181864, 9539612, 6556882, 5692135, 8389632] hf hy hc (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_line_products
    monsterCo1GeometryVectorPoint15Transport monsterCo1GeometryVectorPoint41Transport 1
    monsterCo1GeometryVectorPoint15Matrix monsterCo1GeometryVectorPoint15InverseMatrix
    monsterCo1GeometryVectorPoint41Matrix
    monsterCo1GeometryVectorPoint90AfterSignMatrix
    monsterCo1GeometryVectorPoint90AfterInverseMatrix monsterCo1GeometryVectorPoint90Matrix
    monsterCo1GeometryVectorPoint15Transport_binary
    monsterCo1GeometryVectorPoint15Transport_inverse_binary
    monsterCo1GeometryVectorPoint41Transport_binary
    hc1 hc2 hc3 v

/-- The displayed inverse matrix of actual source transport 90. -/
def monsterCo1GeometryVectorPoint90InverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![4130239, 1785887, 5706941, 2586015, 8388882, 1117, 8390287, 161, 1510, 652, 8390335,
      15452462, 1068, 1614, 8390012, 8388993, 6333218, 4756642, 337548, 1373696, 49152,
      4211725, 1436211, 1727]

set_option maxHeartbeats 24000000 in
-- Check all entries of the right inverse before applying actual action injectivity.
/-- The inverse matrix is the inverse of the literal actual Conway transport. -/
theorem monsterCo1GeometryVectorPoint90Transport_inverse_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint90Transport⁻¹ v =
      monsterCo1GeometryVectorPoint90InverseMatrix *ᵥ v := by
  have hm : monsterCo1GeometryVectorPoint90Matrix = monsterCo1GeometryBinaryMaskMatrix
      ![49312, 34000, 8431488, 8390064, 8451136, 8450048, 54464, 8400928, 29824, 8425488,
        8405552, 12910604, 5176840, 14007346, 16185927, 15137351, 4455428, 14179381, 1179654,
        8181864, 9539612, 6556882, 5692135, 8389632] := by rfl
  have hmi : monsterCo1GeometryVectorPoint90InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
      ![4130239, 1785887, 5706941, 2586015, 8388882, 1117, 8390287, 161, 1510, 652, 8390335,
        15452462, 1068, 1614, 8390012, 8388993, 6333218, 4756642, 337548, 1373696, 49152,
        4211725, 1436211, 1727] := by rfl
  have hi : (1 : Matrix (Fin 24) (Fin 24) (ZMod 2)) = monsterCo1GeometryBinaryMaskMatrix
      ![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536,
        131072, 262144, 524288, 1048576, 2097152, 4194304, 8388608] := by decide +kernel
  have hc : monsterCo1GeometryVectorPoint90Matrix *
    monsterCo1GeometryVectorPoint90InverseMatrix = 1 :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
      ![49312, 34000, 8431488, 8390064, 8451136, 8450048, 54464, 8400928, 29824, 8425488,
        8405552, 12910604, 5176840, 14007346, 16185927, 15137351, 4455428, 14179381, 1179654,
        8181864, 9539612, 6556882, 5692135, 8389632]
      ![4130239, 1785887, 5706941, 2586015, 8388882, 1117, 8390287, 161, 1510, 652, 8390335,
        15452462, 1068, 1614, 8390012, 8388993, 6333218, 4756642, 337548, 1373696, 49152,
        4211725, 1436211, 1727]
      ![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536,
        131072, 262144, 524288, 1048576, 2097152, 4194304, 8388608] hm hmi hi
      (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_inv monsterCo1GeometryVectorPoint90Transport _ _
    monsterCo1GeometryVectorPoint90Transport_binary hc v

/-- Source point 90 is the literal actual transported frame point. -/
def monsterCo1GeometryVectorPoint90 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryVectorPoint90Transport • monsterCo1GeometryBasePoint

/-- Complete binary coordinates of this literal actual source point. -/
theorem monsterCo1GeometryVectorPoint90_binary :
    monsterCo1GeometryVectorPoint90.val =
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 0] := by
  change co1BinaryAction monsterCo1GeometryVectorPoint90Transport monsterCo1GeometryBasePoint.val =
      _
  rw [monsterCo1GeometryVectorPoint90Transport_binary, monsterCo1GeometryBasePoint_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
