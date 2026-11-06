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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint057

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The literal actual two-core word for source point 102. -/
def monsterCo1GeometryVectorPoint102Transport : Co1 :=
  monsterCo1GeometryVectorPoint11Transport * monsterCo1GeometryTransportOperator 6 *
    monsterCo1GeometryVectorPoint11Transport⁻¹ * monsterCo1GeometryVectorPoint57Transport

/-- Complete displayed binary matrix of actual transport 102. -/
def monsterCo1GeometryVectorPoint102Matrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![12742900, 8902496, 3429399, 2618391, 13064409, 4677242, 338639, 338511, 12618749,
      12617790, 9676503, 5450516, 8873588, 8818904, 8616308, 8616820, 8842133, 466230,
      13584682, 13117673, 477283, 428259, 8662179, 480471]

/-- First complete finite matrix product in literal actual transport 102. -/
def monsterCo1GeometryVectorPoint102AfterSignMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![8438240, 33280, 11560346, 10512220, 12758976, 4370353, 12742144, 12742353, 12766656,
      4377953, 9438918, 4655367, 10355910, 327945, 8907287, 8906775, 8646661, 528662, 8581126,
      791056, 12795234, 13033174, 469751, 8446992]

/-- Second complete finite matrix product in literal actual transport 102. -/
def monsterCo1GeometryVectorPoint102AfterInverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![8339843, 12567614, 12333451, 991401, 6470428, 14531616, 10681794, 10681602, 14842914,
      6125614, 11736366, 6187521, 8443438, 8157613, 6365203, 6414355, 77484, 7512595, 262144,
      316690, 5067906, 8456241, 6168977, 12517906]

set_option maxHeartbeats 24000000 in
-- Check every entry of this finite actual transport matrix in the Lean kernel.
/-- Every column of transport 102 is its actual Conway binary action. -/
theorem monsterCo1GeometryVectorPoint102Transport_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint102Transport v =
      monsterCo1GeometryVectorPoint102Matrix *ᵥ v := by
  have hx : monsterCo1GeometryVectorPoint11Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![49312, 8421584, 11560912, 10511824, 12627023, 12627006, 12610767, 12610590, 12635279,
    12635182, 9438720, 4524557, 10356230, 328204, 387341, 387853, 8646666, 8917002, 8581126,
    9179142, 4275234, 4512899, 338093, 58368] := by decide +kernel
  have hxi : monsterCo1GeometryVectorPoint11InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![1008, 1035612, 3988060, 3357276, 8389918, 81, 8390287, 161, 4210689, 49152, 12518144,
    8380657, 9766412, 4129777, 12518607, 12518462, 712704, 2233600, 385024, 1373696, 49164,
    12599307, 8375041, 12519180] := by decide +kernel
  have hy : monsterCo1GeometryVectorPoint57Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![1041, 513571, 11006217, 11007854, 8447136, 58400, 8447088, 8447216, 26272, 25408,
    8388784, 14099015, 14160, 1552, 8256, 8768, 5352069, 12938698, 13584682, 6000589, 1106445,
    9495041, 12910962, 1200] := by decide +kernel
  have he : monsterCo1GeometryVectorPoint102AfterSignMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![8438240, 33280, 11560346, 10512220, 12758976, 4370353, 12742144, 12742353, 12766656,
    4377953, 9438918, 4655367, 10355910, 327945, 8907287, 8906775, 8646661, 528662, 8581126,
    791056, 12795234, 13033174, 469751, 8446992] := by rfl
  have hf : monsterCo1GeometryVectorPoint102AfterInverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![8339843, 12567614, 12333451, 991401, 6470428, 14531616, 10681794, 10681602, 14842914,
    6125614, 11736366, 6187521, 8443438, 8157613, 6365203, 6414355, 77484, 7512595, 262144,
    316690, 5067906, 8456241, 6168977, 12517906] := by rfl
  have hc : monsterCo1GeometryVectorPoint102Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![12742900, 8902496, 3429399, 2618391, 13064409, 4677242, 338639, 338511, 12618749,
    12617790, 9676503, 5450516, 8873588, 8818904, 8616308, 8616820, 8842133, 466230, 13584682,
    13117673, 477283, 428259, 8662179, 480471] := by rfl
  have hc1 : monsterCo1GeometryVectorPoint11Matrix *
    monsterCo1GeometryTransportOperatorMatrix 6 =
    monsterCo1GeometryVectorPoint102AfterSignMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![49312, 8421584, 11560912, 10511824, 12627023, 12627006, 12610767, 12610590, 12635279,
    12635182, 9438720, 4524557, 10356230, 328204, 387341, 387853, 8646666, 8917002, 8581126,
    9179142, 4275234, 4512899, 338093, 58368]
      (monsterCo1GeometryBinaryOperatorMasks 6)
    ![8438240, 33280, 11560346, 10512220, 12758976, 4370353, 12742144, 12742353, 12766656,
    4377953, 9438918, 4655367, 10355910, 327945, 8907287, 8906775, 8646661, 528662, 8581126,
    791056, 12795234, 13033174, 469751, 8446992] hx
    (monsterCo1GeometryBinaryOperatorMasks_decode 6) he (by decide +kernel)
  have hc2 : monsterCo1GeometryVectorPoint102AfterSignMatrix *
    monsterCo1GeometryVectorPoint11InverseMatrix =
    monsterCo1GeometryVectorPoint102AfterInverseMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![8438240, 33280, 11560346, 10512220, 12758976, 4370353, 12742144, 12742353, 12766656,
    4377953, 9438918, 4655367, 10355910, 327945, 8907287, 8906775, 8646661, 528662, 8581126,
    791056, 12795234, 13033174, 469751, 8446992]
    ![1008, 1035612, 3988060, 3357276, 8389918, 81, 8390287, 161, 4210689, 49152, 12518144,
    8380657, 9766412, 4129777, 12518607, 12518462, 712704, 2233600, 385024, 1373696, 49164,
    12599307, 8375041, 12519180]
    ![8339843, 12567614, 12333451, 991401, 6470428, 14531616, 10681794, 10681602, 14842914,
    6125614, 11736366, 6187521, 8443438, 8157613, 6365203, 6414355, 77484, 7512595, 262144,
    316690, 5067906, 8456241, 6168977, 12517906] he hxi hf (by decide +kernel)
  have hc3 : monsterCo1GeometryVectorPoint102AfterInverseMatrix *
    monsterCo1GeometryVectorPoint57Matrix = monsterCo1GeometryVectorPoint102Matrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![8339843, 12567614, 12333451, 991401, 6470428, 14531616, 10681794, 10681602, 14842914,
    6125614, 11736366, 6187521, 8443438, 8157613, 6365203, 6414355, 77484, 7512595, 262144,
    316690, 5067906, 8456241, 6168977, 12517906]
    ![1041, 513571, 11006217, 11007854, 8447136, 58400, 8447088, 8447216, 26272, 25408,
    8388784, 14099015, 14160, 1552, 8256, 8768, 5352069, 12938698, 13584682, 6000589, 1106445,
    9495041, 12910962, 1200]
    ![12742900, 8902496, 3429399, 2618391, 13064409, 4677242, 338639, 338511, 12618749,
    12617790, 9676503, 5450516, 8873588, 8818904, 8616308, 8616820, 8842133, 466230, 13584682,
    13117673, 477283, 428259, 8662179, 480471] hf hy hc (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_line_products
    monsterCo1GeometryVectorPoint11Transport monsterCo1GeometryVectorPoint57Transport 6
    monsterCo1GeometryVectorPoint11Matrix monsterCo1GeometryVectorPoint11InverseMatrix
    monsterCo1GeometryVectorPoint57Matrix
    monsterCo1GeometryVectorPoint102AfterSignMatrix
    monsterCo1GeometryVectorPoint102AfterInverseMatrix monsterCo1GeometryVectorPoint102Matrix
    monsterCo1GeometryVectorPoint11Transport_binary
    monsterCo1GeometryVectorPoint11Transport_inverse_binary
    monsterCo1GeometryVectorPoint57Transport_binary
    hc1 hc2 hc3 v

/-- Source point 102 is the literal actual transported frame point. -/
def monsterCo1GeometryVectorPoint102 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryVectorPoint102Transport • monsterCo1GeometryBasePoint

/-- Complete binary coordinates of this literal actual source point. -/
theorem monsterCo1GeometryVectorPoint102_binary :
    monsterCo1GeometryVectorPoint102.val =
      ![0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0] := by
  change co1BinaryAction monsterCo1GeometryVectorPoint102Transport monsterCo1GeometryBasePoint.val =
      _
  rw [monsterCo1GeometryVectorPoint102Transport_binary, monsterCo1GeometryBasePoint_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
