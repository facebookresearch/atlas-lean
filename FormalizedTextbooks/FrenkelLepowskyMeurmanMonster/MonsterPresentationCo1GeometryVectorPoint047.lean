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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint003
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint015

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The literal actual two-core word for source point 47. -/
def monsterCo1GeometryVectorPoint47Transport : Co1 :=
  monsterCo1GeometryVectorPoint3Transport * monsterCo1GeometryTransportOperator 1 *
    monsterCo1GeometryVectorPoint3Transport⁻¹ * monsterCo1GeometryVectorPoint15Transport

/-- Complete displayed binary matrix of actual transport 47. -/
def monsterCo1GeometryVectorPoint47Matrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  ![![0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 1, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1],
    ![0, 0, 0, 0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1],
    ![1, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1],
    ![0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1],
    ![1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1],
    ![0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1],
    ![1, 1, 1, 1, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1],
    ![0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1],
    ![1, 1, 1, 0, 0, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0],
    ![0, 0, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0],
    ![0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 0, 0, 1, 1, 1, 0, 1, 0, 0, 0, 1, 1],
    ![0, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0],
    ![0, 1, 0, 0, 1, 0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0],
    ![0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0],
    ![0, 1, 0, 1, 1, 1, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0],
    ![0, 0, 0, 1, 1, 1, 0, 0, 0, 1, 1, 1, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1],
    ![1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 0, 1],
    ![0, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0],
    ![0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0],
    ![0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]]

/-- First complete finite matrix product in literal actual transport 47. -/
def monsterCo1GeometryVectorPoint47AfterSignMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
    ![0, 0, 1, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0],
    ![0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0],
    ![1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1],
    ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1],
    ![0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0],
    ![1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0],
    ![0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]]

/-- Second complete finite matrix product in literal actual transport 47. -/
def monsterCo1GeometryVectorPoint47AfterInverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0],
    ![0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
    ![0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
    ![1, 0, 1, 1, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
    ![0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]]

set_option maxHeartbeats 24000000 in
-- Check every entry of this finite actual transport matrix in the Lean kernel.
/-- Every column of transport 47 is its actual Conway binary action. -/
theorem monsterCo1GeometryVectorPoint47Transport_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint47Transport v =
      monsterCo1GeometryVectorPoint47Matrix *ᵥ v := by
  have hx : monsterCo1GeometryVectorPoint3Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![768, 256, 33280, 16896, 53520, 12608, 53792, 12928, 53248, 12288, 8437760, 4194304,
    2752604, 4129020, 4196363, 4196359, 78336, 315904, 143616, 577792, 209091, 839730, 4196352,
    8389632] := by decide +kernel
  have hxi : monsterCo1GeometryVectorPoint3InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![4129776, 2752848, 5604000, 5587616, 274, 323, 546, 643, 2, 3, 8389644, 4196352, 268, 780,
    11, 7, 66051, 262658, 131331, 524546, 209088, 839728, 2048, 1036] := by decide +kernel
  have hy : monsterCo1GeometryVectorPoint15Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![49312, 8421584, 11560912, 10511824, 12601423, 12627006, 12610767, 12610590, 12635279,
    12635182, 9438720, 5683319, 6180408, 12970498, 355693, 380765, 8646666, 1593978, 5389864,
    12384167, 9523772, 6568274, 338093, 58368] := by decide +kernel
  have he : monsterCo1GeometryVectorPoint47AfterSignMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![768, 256, 8422912, 8406528, 53520, 8402240, 53792, 8402560, 53248, 8401920, 8437760,
    4194318, 2752844, 4129740, 12589067, 12589063, 8468000, 315904, 8533264, 577792, 210163,
    839730, 4200448, 8389632] := by decide +kernel
  have hf : monsterCo1GeometryVectorPoint47AfterInverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![1, 2, 8388612, 8388616, 16, 8388640, 64, 8388736, 256, 8389120, 1024, 2804048, 4368,
    8272, 17664, 34048, 8454467, 131072, 8651026, 524288, 9438301, 2097152, 4194572, 8388608]
    := by decide +kernel
  have hc : monsterCo1GeometryVectorPoint47Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![49312, 8421584, 11568080, 10518992, 12601423, 12601406, 12610767, 12617758, 12635279,
    12593198, 9438720, 5664455, 6212344, 12963458, 5613538, 5572050, 259130, 1593978, 13819448,
    12384167, 1136156, 6568274, 14018082, 58368] := by decide +kernel
  have hc1 : monsterCo1GeometryVectorPoint3Matrix * monsterCo1GeometryTransportOperatorMatrix
    1 = monsterCo1GeometryVectorPoint47AfterSignMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![768, 256, 33280, 16896, 53520, 12608, 53792, 12928, 53248, 12288, 8437760, 4194304,
    2752604, 4129020, 4196363, 4196359, 78336, 315904, 143616, 577792, 209091, 839730, 4196352,
    8389632]
      (monsterCo1GeometryBinaryOperatorMasks 1)
    ![768, 256, 8422912, 8406528, 53520, 8402240, 53792, 8402560, 53248, 8401920, 8437760,
    4194318, 2752844, 4129740, 12589067, 12589063, 8468000, 315904, 8533264, 577792, 210163,
    839730, 4200448, 8389632] hx (monsterCo1GeometryBinaryOperatorMasks_decode 1) he
      (by decide +kernel)
  have hc2 : monsterCo1GeometryVectorPoint47AfterSignMatrix *
    monsterCo1GeometryVectorPoint3InverseMatrix =
    monsterCo1GeometryVectorPoint47AfterInverseMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![768, 256, 8422912, 8406528, 53520, 8402240, 53792, 8402560, 53248, 8401920, 8437760,
    4194318, 2752844, 4129740, 12589067, 12589063, 8468000, 315904, 8533264, 577792, 210163,
    839730, 4200448, 8389632]
    ![4129776, 2752848, 5604000, 5587616, 274, 323, 546, 643, 2, 3, 8389644, 4196352, 268, 780,
    11, 7, 66051, 262658, 131331, 524546, 209088, 839728, 2048, 1036]
    ![1, 2, 8388612, 8388616, 16, 8388640, 64, 8388736, 256, 8389120, 1024, 2804048, 4368,
    8272, 17664, 34048, 8454467, 131072, 8651026, 524288, 9438301, 2097152, 4194572, 8388608]
    he hxi hf (by decide +kernel)
  have hc3 : monsterCo1GeometryVectorPoint47AfterInverseMatrix *
    monsterCo1GeometryVectorPoint15Matrix = monsterCo1GeometryVectorPoint47Matrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![1, 2, 8388612, 8388616, 16, 8388640, 64, 8388736, 256, 8389120, 1024, 2804048, 4368,
    8272, 17664, 34048, 8454467, 131072, 8651026, 524288, 9438301, 2097152, 4194572, 8388608]
    ![49312, 8421584, 11560912, 10511824, 12601423, 12627006, 12610767, 12610590, 12635279,
    12635182, 9438720, 5683319, 6180408, 12970498, 355693, 380765, 8646666, 1593978, 5389864,
    12384167, 9523772, 6568274, 338093, 58368]
    ![49312, 8421584, 11568080, 10518992, 12601423, 12601406, 12610767, 12617758, 12635279,
    12593198, 9438720, 5664455, 6212344, 12963458, 5613538, 5572050, 259130, 1593978, 13819448,
    12384167, 1136156, 6568274, 14018082, 58368] hf hy hc (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_line_products
    monsterCo1GeometryVectorPoint3Transport monsterCo1GeometryVectorPoint15Transport 1
    monsterCo1GeometryVectorPoint3Matrix monsterCo1GeometryVectorPoint3InverseMatrix
    monsterCo1GeometryVectorPoint15Matrix
    monsterCo1GeometryVectorPoint47AfterSignMatrix
    monsterCo1GeometryVectorPoint47AfterInverseMatrix monsterCo1GeometryVectorPoint47Matrix
    monsterCo1GeometryVectorPoint3Transport_binary
    monsterCo1GeometryVectorPoint3Transport_inverse_binary
    monsterCo1GeometryVectorPoint15Transport_binary
    hc1 hc2 hc3 v

/-- The displayed inverse matrix of actual source transport 47. -/
def monsterCo1GeometryVectorPoint47InverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  ![![0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1],
    ![1, 1, 0, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 0, 0, 1, 1, 1, 0, 1, 0, 0, 1],
    ![1, 1, 1, 0, 1, 0, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 0, 0, 0],
    ![0, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1],
    ![0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1, 1, 1, 1, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1],
    ![0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 1],
    ![0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1],
    ![1, 0, 0, 0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0],
    ![1, 0, 0, 1, 1, 1, 1, 0, 1, 1, 0, 0, 0, 1, 1, 1, 0, 1, 0, 1, 0, 0, 0, 0],
    ![1, 0, 1, 0, 1, 1, 1, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0],
    ![1, 0, 1, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 1, 1, 1, 0, 1, 0, 0, 0, 0, 1],
    ![1, 1, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 0, 1, 0, 0, 1],
    ![0, 0, 1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1, 1, 1, 0, 0, 1, 1, 1, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1],
    ![0, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1],
    ![1, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1]]

set_option maxHeartbeats 24000000 in
-- Check all entries of the right inverse before applying actual action injectivity.
/-- The inverse matrix is the inverse of the literal actual Conway transport. -/
theorem monsterCo1GeometryVectorPoint47Transport_inverse_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint47Transport⁻¹ v =
      monsterCo1GeometryVectorPoint47InverseMatrix *ᵥ v := by
  have hm : monsterCo1GeometryVectorPoint47Matrix = monsterCo1GeometryBinaryMaskMatrix
      ![49312, 8421584, 11568080, 10518992, 12601423, 12601406, 12610767, 12617758, 12635279,
        12593198, 9438720, 5664455, 6212344, 12963458, 5613538, 5572050, 259130, 1593978,
        13819448, 12384167, 1136156, 6568274, 14018082, 58368] := by decide +kernel
  have hmi : monsterCo1GeometryVectorPoint47InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
      ![1008, 10751636, 9903603, 1637591, 1310, 8388689, 8390287, 161, 12600813, 49792,
        12518991, 8381634, 9764992, 12519102, 12517760, 4129137, 713593, 2233589, 8774189,
        9760911, 49804, 12600807, 13897182, 12517955] := by decide +kernel
  have hi : (1 : Matrix (Fin 24) (Fin 24) (ZMod 2)) = monsterCo1GeometryBinaryMaskMatrix
      ![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536,
        131072, 262144, 524288, 1048576, 2097152, 4194304, 8388608] := by decide +kernel
  have hc : monsterCo1GeometryVectorPoint47Matrix *
    monsterCo1GeometryVectorPoint47InverseMatrix = 1 :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
      ![49312, 8421584, 11568080, 10518992, 12601423, 12601406, 12610767, 12617758, 12635279,
        12593198, 9438720, 5664455, 6212344, 12963458, 5613538, 5572050, 259130, 1593978,
        13819448, 12384167, 1136156, 6568274, 14018082, 58368]
      ![1008, 10751636, 9903603, 1637591, 1310, 8388689, 8390287, 161, 12600813, 49792,
        12518991, 8381634, 9764992, 12519102, 12517760, 4129137, 713593, 2233589, 8774189,
        9760911, 49804, 12600807, 13897182, 12517955]
      ![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536,
        131072, 262144, 524288, 1048576, 2097152, 4194304, 8388608] hm hmi hi
      (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_inv monsterCo1GeometryVectorPoint47Transport _ _
    monsterCo1GeometryVectorPoint47Transport_binary hc v

/-- Source point 47 is the literal actual transported frame point. -/
def monsterCo1GeometryVectorPoint47 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryVectorPoint47Transport • monsterCo1GeometryBasePoint

/-- Complete binary coordinates of this literal actual source point. -/
theorem monsterCo1GeometryVectorPoint47_binary :
    monsterCo1GeometryVectorPoint47.val =
      ![0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0] := by
  change co1BinaryAction monsterCo1GeometryVectorPoint47Transport monsterCo1GeometryBasePoint.val =
      _
  rw [monsterCo1GeometryVectorPoint47Transport_binary, monsterCo1GeometryBasePoint_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
