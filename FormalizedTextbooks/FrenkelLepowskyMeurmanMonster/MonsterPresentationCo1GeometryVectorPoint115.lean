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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint011
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint069

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The literal actual two-core word for source point 115. -/
def monsterCo1GeometryVectorPoint115Transport : Co1 :=
  monsterCo1GeometryVectorPoint11Transport * monsterCo1GeometryTransportOperator 1 *
    monsterCo1GeometryVectorPoint11Transport⁻¹ * monsterCo1GeometryVectorPoint69Transport

/-- Complete displayed binary matrix of actual transport 115. -/
def monsterCo1GeometryVectorPoint115Matrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![49312, 8421584, 8431488, 432, 61504, 8450048, 54464, 8400928, 29824, 8425488, 8405552,
      3477261, 5114376, 14003762, 7773735, 6715431, 12807268, 14184133, 1189622, 8163320,
      9557644, 6585778, 5660551, 8389632]

/-- First complete finite matrix product in literal actual transport 115. -/
def monsterCo1GeometryVectorPoint115AfterSignMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![49312, 34000, 11560144, 10511568, 4242511, 12631102, 4226255, 12614686, 4250767,
      12639278, 9438208, 12917293, 10355734, 328236, 392483, 392995, 259130, 8917002, 193558,
      9179142, 12658690, 12897411, 343171, 8445952]

/-- Second complete finite matrix product in literal actual transport 115. -/
def monsterCo1GeometryVectorPoint115AfterInverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![1, 1038, 4227077, 4210697, 2752784, 9766444, 2752832, 9766540, 2752512, 9765900, 50176,
      2754897, 8443166, 8273, 2779137, 2795521, 8454467, 131072, 8651026, 524288, 8716881,
      655616, 6957057, 8389644]

set_option maxHeartbeats 24000000 in
-- Check every entry of this finite actual transport matrix in the Lean kernel.
/-- Every column of transport 115 is its actual Conway binary action. -/
theorem monsterCo1GeometryVectorPoint115Transport_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint115Transport v =
      monsterCo1GeometryVectorPoint115Matrix *ᵥ v := by
  have hx : monsterCo1GeometryVectorPoint11Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![49312, 8421584, 11560912, 10511824, 12627023, 12627006, 12610767, 12610590, 12635279,
    12635182, 9438720, 4524557, 10356230, 328204, 387341, 387853, 8646666, 8917002, 8581126,
    9179142, 4275234, 4512899, 338093, 58368] := by decide +kernel
  have hxi : monsterCo1GeometryVectorPoint11InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![1008, 1035612, 3988060, 3357276, 8389918, 81, 8390287, 161, 4210689, 49152, 12518144,
    8380657, 9766412, 4129777, 12518607, 12518462, 712704, 2233600, 385024, 1373696, 49164,
    12599307, 8375041, 12519180] := by decide +kernel
  have hy : monsterCo1GeometryVectorPoint69Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![49312, 8414416, 11550848, 2097328, 12589135, 12590094, 12598479, 12639278, 12622991,
    12614686, 9479216, 16057122, 6162456, 13978130, 5661495, 4621623, 12814420, 14184133,
    1189606, 8163320, 13712034, 10786237, 7774871, 8445952] := by decide +kernel
  have he : monsterCo1GeometryVectorPoint115AfterSignMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![49312, 34000, 11560144, 10511568, 4242511, 12631102, 4226255, 12614686, 4250767,
    12639278, 9438208, 12917293, 10355734, 328236, 392483, 392995, 259130, 8917002, 193558,
    9179142, 12658690, 12897411, 343171, 8445952] := by rfl
  have hf : monsterCo1GeometryVectorPoint115AfterInverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![1, 1038, 4227077, 4210697, 2752784, 9766444, 2752832, 9766540, 2752512, 9765900, 50176,
    2754897, 8443166, 8273, 2779137, 2795521, 8454467, 131072, 8651026, 524288, 8716881,
    655616, 6957057, 8389644] := by rfl
  have hc : monsterCo1GeometryVectorPoint115Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![49312, 8421584, 8431488, 432, 61504, 8450048, 54464, 8400928, 29824, 8425488, 8405552,
    3477261, 5114376, 14003762, 7773735, 6715431, 12807268, 14184133, 1189622, 8163320,
    9557644, 6585778, 5660551, 8389632] := by rfl
  have hc1 : monsterCo1GeometryVectorPoint11Matrix *
    monsterCo1GeometryTransportOperatorMatrix 1 =
    monsterCo1GeometryVectorPoint115AfterSignMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![49312, 8421584, 11560912, 10511824, 12627023, 12627006, 12610767, 12610590, 12635279,
    12635182, 9438720, 4524557, 10356230, 328204, 387341, 387853, 8646666, 8917002, 8581126,
    9179142, 4275234, 4512899, 338093, 58368]
      (monsterCo1GeometryBinaryOperatorMasks 1)
    ![49312, 34000, 11560144, 10511568, 4242511, 12631102, 4226255, 12614686, 4250767,
    12639278, 9438208, 12917293, 10355734, 328236, 392483, 392995, 259130, 8917002, 193558,
    9179142, 12658690, 12897411, 343171, 8445952] hx
    (monsterCo1GeometryBinaryOperatorMasks_decode 1) he (by decide +kernel)
  have hc2 : monsterCo1GeometryVectorPoint115AfterSignMatrix *
    monsterCo1GeometryVectorPoint11InverseMatrix =
    monsterCo1GeometryVectorPoint115AfterInverseMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![49312, 34000, 11560144, 10511568, 4242511, 12631102, 4226255, 12614686, 4250767,
    12639278, 9438208, 12917293, 10355734, 328236, 392483, 392995, 259130, 8917002, 193558,
    9179142, 12658690, 12897411, 343171, 8445952]
    ![1008, 1035612, 3988060, 3357276, 8389918, 81, 8390287, 161, 4210689, 49152, 12518144,
    8380657, 9766412, 4129777, 12518607, 12518462, 712704, 2233600, 385024, 1373696, 49164,
    12599307, 8375041, 12519180]
    ![1, 1038, 4227077, 4210697, 2752784, 9766444, 2752832, 9766540, 2752512, 9765900, 50176,
    2754897, 8443166, 8273, 2779137, 2795521, 8454467, 131072, 8651026, 524288, 8716881,
    655616, 6957057, 8389644] he hxi hf (by decide +kernel)
  have hc3 : monsterCo1GeometryVectorPoint115AfterInverseMatrix *
    monsterCo1GeometryVectorPoint69Matrix = monsterCo1GeometryVectorPoint115Matrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![1, 1038, 4227077, 4210697, 2752784, 9766444, 2752832, 9766540, 2752512, 9765900, 50176,
    2754897, 8443166, 8273, 2779137, 2795521, 8454467, 131072, 8651026, 524288, 8716881,
    655616, 6957057, 8389644]
    ![49312, 8414416, 11550848, 2097328, 12589135, 12590094, 12598479, 12639278, 12622991,
    12614686, 9479216, 16057122, 6162456, 13978130, 5661495, 4621623, 12814420, 14184133,
    1189606, 8163320, 13712034, 10786237, 7774871, 8445952]
    ![49312, 8421584, 8431488, 432, 61504, 8450048, 54464, 8400928, 29824, 8425488, 8405552,
    3477261, 5114376, 14003762, 7773735, 6715431, 12807268, 14184133, 1189622, 8163320,
    9557644, 6585778, 5660551, 8389632] hf hy hc (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_line_products
    monsterCo1GeometryVectorPoint11Transport monsterCo1GeometryVectorPoint69Transport 1
    monsterCo1GeometryVectorPoint11Matrix monsterCo1GeometryVectorPoint11InverseMatrix
    monsterCo1GeometryVectorPoint69Matrix
    monsterCo1GeometryVectorPoint115AfterSignMatrix
    monsterCo1GeometryVectorPoint115AfterInverseMatrix monsterCo1GeometryVectorPoint115Matrix
    monsterCo1GeometryVectorPoint11Transport_binary
    monsterCo1GeometryVectorPoint11Transport_inverse_binary
    monsterCo1GeometryVectorPoint69Transport_binary
    hc1 hc2 hc3 v

/-- Source point 115 is the literal actual transported frame point. -/
def monsterCo1GeometryVectorPoint115 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryVectorPoint115Transport • monsterCo1GeometryBasePoint

/-- Complete binary coordinates of this literal actual source point. -/
theorem monsterCo1GeometryVectorPoint115_binary :
    monsterCo1GeometryVectorPoint115.val =
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 0] := by
  change co1BinaryAction monsterCo1GeometryVectorPoint115Transport monsterCo1GeometryBasePoint.val =
      _
  rw [monsterCo1GeometryVectorPoint115Transport_binary, monsterCo1GeometryBasePoint_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
