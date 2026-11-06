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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint154

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The literal actual two-core word for source point 157. -/
def monsterCo1GeometryVectorPoint157Transport : Co1 :=
  monsterCo1GeometryVectorPoint11Transport * monsterCo1GeometryTransportOperator 1 *
    monsterCo1GeometryVectorPoint11Transport⁻¹ * monsterCo1GeometryVectorPoint154Transport

/-- Complete displayed binary matrix of actual transport 157. -/
def monsterCo1GeometryVectorPoint157Matrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![11585126, 50896, 6244257, 6083800, 13782278, 15559943, 6459245, 14527232, 13798614,
      13799221, 12367787, 6637935, 5422278, 16447043, 6298082, 13847744, 1981298, 14029475,
      4017152, 1021609, 1880909, 15090888, 789505, 4138018]

/-- First complete finite matrix product in literal actual transport 157. -/
def monsterCo1GeometryVectorPoint157AfterSignMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![49312, 34000, 11560144, 10511568, 4242511, 12631102, 4226255, 12614686, 4250767,
      12639278, 9438208, 12917293, 10355734, 328236, 392483, 392995, 259130, 8917002, 193558,
      9179142, 12658690, 12897411, 343171, 8445952]

/-- Second complete finite matrix product in literal actual transport 157. -/
def monsterCo1GeometryVectorPoint157AfterInverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![1, 1038, 4227077, 4210697, 2752784, 9766444, 2752832, 9766540, 2752512, 9765900, 50176,
      2754897, 8443166, 8273, 2779137, 2795521, 8454467, 131072, 8651026, 524288, 8716881,
      655616, 6957057, 8389644]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 24000000 in
-- Check every entry of this finite actual transport matrix in the Lean kernel.
/-- Every column of transport 157 is its actual Conway binary action. -/
theorem monsterCo1GeometryVectorPoint157Transport_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint157Transport v =
      monsterCo1GeometryVectorPoint157Matrix *ᵥ v := by
  have hx : monsterCo1GeometryVectorPoint11Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![49312, 8421584, 11560912, 10511824, 12627023, 12627006, 12610767, 12610590, 12635279,
    12635182, 9438720, 4524557, 10356230, 328204, 387341, 387853, 8646666, 8917002, 8581126,
    9179142, 4275234, 4512899, 338093, 58368] := by decide +kernel
  have hxi : monsterCo1GeometryVectorPoint11InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![1008, 1035612, 3988060, 3357276, 8389918, 81, 8390287, 161, 4210689, 49152, 12518144,
    8380657, 9766412, 4129777, 12518607, 12518462, 712704, 2233600, 385024, 1373696, 49164,
    12599307, 8375041, 12519180] := by decide +kernel
  have hy : monsterCo1GeometryVectorPoint154Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![11585126, 12575234, 3195142, 8390493, 4129042, 8398589, 9421689, 11591930, 4178114,
    12567759, 1041033, 8913270, 6417940, 16446030, 7381098, 12842312, 2169949, 14029475,
    159522, 1021609, 13555816, 723164, 1881481, 8388848] := by rfl
  have he : monsterCo1GeometryVectorPoint157AfterSignMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![49312, 34000, 11560144, 10511568, 4242511, 12631102, 4226255, 12614686, 4250767,
    12639278, 9438208, 12917293, 10355734, 328236, 392483, 392995, 259130, 8917002, 193558,
    9179142, 12658690, 12897411, 343171, 8445952] := by rfl
  have hf : monsterCo1GeometryVectorPoint157AfterInverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![1, 1038, 4227077, 4210697, 2752784, 9766444, 2752832, 9766540, 2752512, 9765900, 50176,
    2754897, 8443166, 8273, 2779137, 2795521, 8454467, 131072, 8651026, 524288, 8716881,
    655616, 6957057, 8389644] := by rfl
  have hc : monsterCo1GeometryVectorPoint157Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![11585126, 50896, 6244257, 6083800, 13782278, 15559943, 6459245, 14527232, 13798614,
    13799221, 12367787, 6637935, 5422278, 16447043, 6298082, 13847744, 1981298, 14029475,
    4017152, 1021609, 1880909, 15090888, 789505, 4138018] := by rfl
  have hc1 : monsterCo1GeometryVectorPoint11Matrix *
    monsterCo1GeometryTransportOperatorMatrix 1 =
    monsterCo1GeometryVectorPoint157AfterSignMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![49312, 8421584, 11560912, 10511824, 12627023, 12627006, 12610767, 12610590, 12635279,
    12635182, 9438720, 4524557, 10356230, 328204, 387341, 387853, 8646666, 8917002, 8581126,
    9179142, 4275234, 4512899, 338093, 58368]
      (monsterCo1GeometryBinaryOperatorMasks 1)
    ![49312, 34000, 11560144, 10511568, 4242511, 12631102, 4226255, 12614686, 4250767,
    12639278, 9438208, 12917293, 10355734, 328236, 392483, 392995, 259130, 8917002, 193558,
    9179142, 12658690, 12897411, 343171, 8445952] hx
    (monsterCo1GeometryBinaryOperatorMasks_decode 1) he (by decide +kernel)
  have hc2 : monsterCo1GeometryVectorPoint157AfterSignMatrix *
    monsterCo1GeometryVectorPoint11InverseMatrix =
    monsterCo1GeometryVectorPoint157AfterInverseMatrix :=
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
  have hc3 : monsterCo1GeometryVectorPoint157AfterInverseMatrix *
    monsterCo1GeometryVectorPoint154Matrix = monsterCo1GeometryVectorPoint157Matrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![1, 1038, 4227077, 4210697, 2752784, 9766444, 2752832, 9766540, 2752512, 9765900, 50176,
    2754897, 8443166, 8273, 2779137, 2795521, 8454467, 131072, 8651026, 524288, 8716881,
    655616, 6957057, 8389644]
    ![11585126, 12575234, 3195142, 8390493, 4129042, 8398589, 9421689, 11591930, 4178114,
    12567759, 1041033, 8913270, 6417940, 16446030, 7381098, 12842312, 2169949, 14029475,
    159522, 1021609, 13555816, 723164, 1881481, 8388848]
    ![11585126, 50896, 6244257, 6083800, 13782278, 15559943, 6459245, 14527232, 13798614,
    13799221, 12367787, 6637935, 5422278, 16447043, 6298082, 13847744, 1981298, 14029475,
    4017152, 1021609, 1880909, 15090888, 789505, 4138018] hf hy hc (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_line_products
    monsterCo1GeometryVectorPoint11Transport monsterCo1GeometryVectorPoint154Transport 1
    monsterCo1GeometryVectorPoint11Matrix monsterCo1GeometryVectorPoint11InverseMatrix
    monsterCo1GeometryVectorPoint154Matrix
    monsterCo1GeometryVectorPoint157AfterSignMatrix
    monsterCo1GeometryVectorPoint157AfterInverseMatrix monsterCo1GeometryVectorPoint157Matrix
    monsterCo1GeometryVectorPoint11Transport_binary
    monsterCo1GeometryVectorPoint11Transport_inverse_binary
    monsterCo1GeometryVectorPoint154Transport_binary
    hc1 hc2 hc3 v

/-- Source point 157 is the literal actual transported frame point. -/
def monsterCo1GeometryVectorPoint157 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryVectorPoint157Transport • monsterCo1GeometryBasePoint

/-- Complete binary coordinates of this literal actual source point. -/
theorem monsterCo1GeometryVectorPoint157_binary :
    monsterCo1GeometryVectorPoint157.val =
      ![0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 0, 1, 0] := by
  change co1BinaryAction monsterCo1GeometryVectorPoint157Transport monsterCo1GeometryBasePoint.val =
      _
  rw [monsterCo1GeometryVectorPoint157Transport_binary, monsterCo1GeometryBasePoint_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
