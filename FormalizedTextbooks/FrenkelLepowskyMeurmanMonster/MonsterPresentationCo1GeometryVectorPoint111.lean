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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint032
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint062

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The literal actual two-core word for source point 111. -/
def monsterCo1GeometryVectorPoint111Transport : Co1 :=
  monsterCo1GeometryVectorPoint32Transport * monsterCo1GeometryTransportOperator 5 *
    monsterCo1GeometryVectorPoint32Transport⁻¹ * monsterCo1GeometryVectorPoint62Transport

/-- Complete displayed binary matrix of actual transport 111. -/
def monsterCo1GeometryVectorPoint111Matrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![26512, 40960, 8396800, 8430432, 20976, 45472, 13984, 8443424, 17152, 9456, 8447520,
      9546335, 16386267, 1050364, 14789860, 8375851, 11989312, 6298687, 6921167, 4133265,
      12835327, 5061243, 3178593, 8389632]

/-- First complete finite matrix product in literal actual transport 111. -/
def monsterCo1GeometryVectorPoint111AfterSignMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![49696, 8422320, 33968, 8422064, 45472, 20976, 29600, 37712, 53792, 8401568, 57888,
      2363332, 975651, 9823404, 15002852, 7604808, 12742436, 4836732, 4443768, 5090396,
      12623869, 12959488, 4508462, 8389632]

/-- Second complete finite matrix product in literal actual transport 111. -/
def monsterCo1GeometryVectorPoint111AfterInverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![8388780, 1754, 1756, 1744, 409, 504, 8388964, 8389109, 1536, 8389293, 8389549, 7084837,
      15270096, 9984, 15488136, 6516756, 780137, 15602256, 976561, 7075653, 13566610, 15786482,
      1106134, 8388608]

set_option maxHeartbeats 24000000 in
-- Check every entry of this finite actual transport matrix in the Lean kernel.
/-- Every column of transport 111 is its actual Conway binary action. -/
theorem monsterCo1GeometryVectorPoint111Transport_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint111Transport v =
      monsterCo1GeometryVectorPoint111Matrix *ᵥ v := by
  have hx : monsterCo1GeometryVectorPoint32Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![49312, 8421584, 34768, 8421840, 8433728, 8409136, 8417472, 8425488, 8441984, 8400928,
    8446464, 2428173, 9363974, 1435148, 6680077, 7669773, 12807268, 13159669, 12766456,
    13413529, 4299954, 4504803, 4574125, 8389632] := by decide +kernel
  have hxi : monsterCo1GeometryVectorPoint32InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![4129536, 6619799, 5641335, 5896167, 8389918, 81, 8390287, 161, 10, 8388620, 2044,
    8366321, 8390316, 769, 8389695, 8389838, 713184, 2234224, 385648, 1374176, 8438784,
    4211719, 8408054, 8390652] := by decide +kernel
  have hy : monsterCo1GeometryVectorPoint62Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![57568, 8417472, 61632, 29600, 32, 57520, 57344, 8388672, 8438480, 41856, 57472, 12583680,
    16052155, 9471788, 3146523, 2131030, 6773501, 3236608, 12083554, 14736124, 11591776,
    3203078, 5082300, 8389632] := by decide +kernel
  have he : monsterCo1GeometryVectorPoint111AfterSignMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![49696, 8422320, 33968, 8422064, 45472, 20976, 29600, 37712, 53792, 8401568, 57888,
    2363332, 975651, 9823404, 15002852, 7604808, 12742436, 4836732, 4443768, 5090396, 12623869,
    12959488, 4508462, 8389632] := by rfl
  have hf : monsterCo1GeometryVectorPoint111AfterInverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![8388780, 1754, 1756, 1744, 409, 504, 8388964, 8389109, 1536, 8389293, 8389549, 7084837,
    15270096, 9984, 15488136, 6516756, 780137, 15602256, 976561, 7075653, 13566610, 15786482,
    1106134, 8388608] := by rfl
  have hc : monsterCo1GeometryVectorPoint111Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![26512, 40960, 8396800, 8430432, 20976, 45472, 13984, 8443424, 17152, 9456, 8447520,
    9546335, 16386267, 1050364, 14789860, 8375851, 11989312, 6298687, 6921167, 4133265,
    12835327, 5061243, 3178593, 8389632] := by rfl
  have hc1 : monsterCo1GeometryVectorPoint32Matrix *
    monsterCo1GeometryTransportOperatorMatrix 5 =
    monsterCo1GeometryVectorPoint111AfterSignMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![49312, 8421584, 34768, 8421840, 8433728, 8409136, 8417472, 8425488, 8441984, 8400928,
    8446464, 2428173, 9363974, 1435148, 6680077, 7669773, 12807268, 13159669, 12766456,
    13413529, 4299954, 4504803, 4574125, 8389632]
      (monsterCo1GeometryBinaryOperatorMasks 5)
    ![49696, 8422320, 33968, 8422064, 45472, 20976, 29600, 37712, 53792, 8401568, 57888,
    2363332, 975651, 9823404, 15002852, 7604808, 12742436, 4836732, 4443768, 5090396, 12623869,
    12959488, 4508462, 8389632] hx (monsterCo1GeometryBinaryOperatorMasks_decode 5) he (by
    decide +kernel)
  have hc2 : monsterCo1GeometryVectorPoint111AfterSignMatrix *
    monsterCo1GeometryVectorPoint32InverseMatrix =
    monsterCo1GeometryVectorPoint111AfterInverseMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![49696, 8422320, 33968, 8422064, 45472, 20976, 29600, 37712, 53792, 8401568, 57888,
    2363332, 975651, 9823404, 15002852, 7604808, 12742436, 4836732, 4443768, 5090396, 12623869,
    12959488, 4508462, 8389632]
    ![4129536, 6619799, 5641335, 5896167, 8389918, 81, 8390287, 161, 10, 8388620, 2044,
    8366321, 8390316, 769, 8389695, 8389838, 713184, 2234224, 385648, 1374176, 8438784,
    4211719, 8408054, 8390652]
    ![8388780, 1754, 1756, 1744, 409, 504, 8388964, 8389109, 1536, 8389293, 8389549, 7084837,
    15270096, 9984, 15488136, 6516756, 780137, 15602256, 976561, 7075653, 13566610, 15786482,
    1106134, 8388608] he hxi hf (by decide +kernel)
  have hc3 : monsterCo1GeometryVectorPoint111AfterInverseMatrix *
    monsterCo1GeometryVectorPoint62Matrix = monsterCo1GeometryVectorPoint111Matrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![8388780, 1754, 1756, 1744, 409, 504, 8388964, 8389109, 1536, 8389293, 8389549, 7084837,
    15270096, 9984, 15488136, 6516756, 780137, 15602256, 976561, 7075653, 13566610, 15786482,
    1106134, 8388608]
    ![57568, 8417472, 61632, 29600, 32, 57520, 57344, 8388672, 8438480, 41856, 57472, 12583680,
    16052155, 9471788, 3146523, 2131030, 6773501, 3236608, 12083554, 14736124, 11591776,
    3203078, 5082300, 8389632]
    ![26512, 40960, 8396800, 8430432, 20976, 45472, 13984, 8443424, 17152, 9456, 8447520,
    9546335, 16386267, 1050364, 14789860, 8375851, 11989312, 6298687, 6921167, 4133265,
    12835327, 5061243, 3178593, 8389632] hf hy hc (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_line_products
    monsterCo1GeometryVectorPoint32Transport monsterCo1GeometryVectorPoint62Transport 5
    monsterCo1GeometryVectorPoint32Matrix monsterCo1GeometryVectorPoint32InverseMatrix
    monsterCo1GeometryVectorPoint62Matrix
    monsterCo1GeometryVectorPoint111AfterSignMatrix
    monsterCo1GeometryVectorPoint111AfterInverseMatrix monsterCo1GeometryVectorPoint111Matrix
    monsterCo1GeometryVectorPoint32Transport_binary
    monsterCo1GeometryVectorPoint32Transport_inverse_binary
    monsterCo1GeometryVectorPoint62Transport_binary
    hc1 hc2 hc3 v

/-- Source point 111 is the literal actual transported frame point. -/
def monsterCo1GeometryVectorPoint111 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryVectorPoint111Transport • monsterCo1GeometryBasePoint

/-- Complete binary coordinates of this literal actual source point. -/
theorem monsterCo1GeometryVectorPoint111_binary :
    monsterCo1GeometryVectorPoint111.val =
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0] := by
  change co1BinaryAction monsterCo1GeometryVectorPoint111Transport monsterCo1GeometryBasePoint.val =
      _
  rw [monsterCo1GeometryVectorPoint111Transport_binary, monsterCo1GeometryBasePoint_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
