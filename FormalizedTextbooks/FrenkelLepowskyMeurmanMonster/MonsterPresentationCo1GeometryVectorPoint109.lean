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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint009
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint061

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The literal actual two-core word for source point 109. -/
def monsterCo1GeometryVectorPoint109Transport : Co1 :=
  monsterCo1GeometryVectorPoint9Transport * monsterCo1GeometryTransportOperator 5 *
    monsterCo1GeometryVectorPoint9Transport⁻¹ * monsterCo1GeometryVectorPoint61Transport

/-- Complete displayed binary matrix of actual transport 109. -/
def monsterCo1GeometryVectorPoint109Matrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![57552, 13349553, 7074506, 8123082, 1152, 8446145, 81, 8445969, 8390364, 1106439, 8388768,
      2566332, 13538546, 1191, 2131900, 10520538, 11279478, 3462808, 11673201, 13246712,
      8414912, 10512106, 1412614, 1137]

/-- First complete finite matrix product in literal actual transport 109. -/
def monsterCo1GeometryVectorPoint109AfterSignMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![161, 12701184, 7465959, 6416747, 1040, 8445968, 57568, 57440, 8422320, 8405392, 8389632,
      5749527, 13703324, 1066349, 2122730, 11584150, 12746548, 1208629, 14278560, 16628571,
      8390299, 3195696, 8661006, 8447008]

/-- Second complete finite matrix product in literal actual transport 109. -/
def monsterCo1GeometryVectorPoint109AfterInverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![1, 855300, 2951653, 10291615, 8447169, 8388624, 58529, 58465, 8422871, 8406171, 1024,
      3379054, 4054796, 11567676, 9496283, 10519767, 3311470, 9193554, 10047292, 3526412,
      9495761, 8389847, 16591837, 8447201]

set_option maxHeartbeats 24000000 in
-- Check every entry of this finite actual transport matrix in the Lean kernel.
/-- Every column of transport 109 is its actual Conway binary action. -/
theorem monsterCo1GeometryVectorPoint109Transport_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint109Transport v =
      monsterCo1GeometryVectorPoint109Matrix *ᵥ v := by
  have hx : monsterCo1GeometryVectorPoint9Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![161, 12635279, 15788942, 14739854, 8389648, 8446000, 8446144, 8446016, 8421584, 8405104,
    8389632, 5683319, 13637695, 9454593, 2121824, 3194960, 12811348, 1209046, 5824133,
    16563192, 1691, 11583990, 338093, 58368] := by decide +kernel
  have hxi : monsterCo1GeometryVectorPoint9InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![8388849, 9358516, 3074686, 10414792, 1040, 8388656, 8389760, 192, 8405739, 49804,
    8446161, 8381075, 8402243, 8446753, 8447601, 58753, 11731897, 10622597, 12321468, 1374176,
    49792, 16864, 4270418, 8447185] := by decide +kernel
  have hy : monsterCo1GeometryVectorPoint61Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![57552, 10026741, 12089582, 11065566, 8388736, 241, 58465, 8389665, 8438204, 9488215,
    8388768, 7656440, 10320518, 34247, 10535100, 10527114, 16770866, 11805592, 6418693,
    10079884, 25280, 10502330, 13001842, 57409] := by decide +kernel
  have he : monsterCo1GeometryVectorPoint109AfterSignMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![161, 12701184, 7465959, 6416747, 1040, 8445968, 57568, 57440, 8422320, 8405392, 8389632,
    5749527, 13703324, 1066349, 2122730, 11584150, 12746548, 1208629, 14278560, 16628571,
    8390299, 3195696, 8661006, 8447008] := by rfl
  have hf : monsterCo1GeometryVectorPoint109AfterInverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![1, 855300, 2951653, 10291615, 8447169, 8388624, 58529, 58465, 8422871, 8406171, 1024,
    3379054, 4054796, 11567676, 9496283, 10519767, 3311470, 9193554, 10047292, 3526412,
    9495761, 8389847, 16591837, 8447201] := by rfl
  have hc : monsterCo1GeometryVectorPoint109Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![57552, 13349553, 7074506, 8123082, 1152, 8446145, 81, 8445969, 8390364, 1106439, 8388768,
    2566332, 13538546, 1191, 2131900, 10520538, 11279478, 3462808, 11673201, 13246712, 8414912,
    10512106, 1412614, 1137] := by rfl
  have hc1 : monsterCo1GeometryVectorPoint9Matrix * monsterCo1GeometryTransportOperatorMatrix
    5 = monsterCo1GeometryVectorPoint109AfterSignMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![161, 12635279, 15788942, 14739854, 8389648, 8446000, 8446144, 8446016, 8421584, 8405104,
    8389632, 5683319, 13637695, 9454593, 2121824, 3194960, 12811348, 1209046, 5824133,
    16563192, 1691, 11583990, 338093, 58368]
      (monsterCo1GeometryBinaryOperatorMasks 5)
    ![161, 12701184, 7465959, 6416747, 1040, 8445968, 57568, 57440, 8422320, 8405392, 8389632,
    5749527, 13703324, 1066349, 2122730, 11584150, 12746548, 1208629, 14278560, 16628571,
    8390299, 3195696, 8661006, 8447008] hx (monsterCo1GeometryBinaryOperatorMasks_decode 5) he
    (by decide +kernel)
  have hc2 : monsterCo1GeometryVectorPoint109AfterSignMatrix *
    monsterCo1GeometryVectorPoint9InverseMatrix =
    monsterCo1GeometryVectorPoint109AfterInverseMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![161, 12701184, 7465959, 6416747, 1040, 8445968, 57568, 57440, 8422320, 8405392, 8389632,
    5749527, 13703324, 1066349, 2122730, 11584150, 12746548, 1208629, 14278560, 16628571,
    8390299, 3195696, 8661006, 8447008]
    ![8388849, 9358516, 3074686, 10414792, 1040, 8388656, 8389760, 192, 8405739, 49804,
    8446161, 8381075, 8402243, 8446753, 8447601, 58753, 11731897, 10622597, 12321468, 1374176,
    49792, 16864, 4270418, 8447185]
    ![1, 855300, 2951653, 10291615, 8447169, 8388624, 58529, 58465, 8422871, 8406171, 1024,
    3379054, 4054796, 11567676, 9496283, 10519767, 3311470, 9193554, 10047292, 3526412,
    9495761, 8389847, 16591837, 8447201] he hxi hf (by decide +kernel)
  have hc3 : monsterCo1GeometryVectorPoint109AfterInverseMatrix *
    monsterCo1GeometryVectorPoint61Matrix = monsterCo1GeometryVectorPoint109Matrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![1, 855300, 2951653, 10291615, 8447169, 8388624, 58529, 58465, 8422871, 8406171, 1024,
    3379054, 4054796, 11567676, 9496283, 10519767, 3311470, 9193554, 10047292, 3526412,
    9495761, 8389847, 16591837, 8447201]
    ![57552, 10026741, 12089582, 11065566, 8388736, 241, 58465, 8389665, 8438204, 9488215,
    8388768, 7656440, 10320518, 34247, 10535100, 10527114, 16770866, 11805592, 6418693,
    10079884, 25280, 10502330, 13001842, 57409]
    ![57552, 13349553, 7074506, 8123082, 1152, 8446145, 81, 8445969, 8390364, 1106439, 8388768,
    2566332, 13538546, 1191, 2131900, 10520538, 11279478, 3462808, 11673201, 13246712, 8414912,
    10512106, 1412614, 1137] hf hy hc (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_line_products
    monsterCo1GeometryVectorPoint9Transport monsterCo1GeometryVectorPoint61Transport 5
    monsterCo1GeometryVectorPoint9Matrix monsterCo1GeometryVectorPoint9InverseMatrix
    monsterCo1GeometryVectorPoint61Matrix
    monsterCo1GeometryVectorPoint109AfterSignMatrix
    monsterCo1GeometryVectorPoint109AfterInverseMatrix monsterCo1GeometryVectorPoint109Matrix
    monsterCo1GeometryVectorPoint9Transport_binary
    monsterCo1GeometryVectorPoint9Transport_inverse_binary
    monsterCo1GeometryVectorPoint61Transport_binary
    hc1 hc2 hc3 v

/-- Source point 109 is the literal actual transported frame point. -/
def monsterCo1GeometryVectorPoint109 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryVectorPoint109Transport • monsterCo1GeometryBasePoint

/-- Complete binary coordinates of this literal actual source point. -/
theorem monsterCo1GeometryVectorPoint109_binary :
    monsterCo1GeometryVectorPoint109.val =
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0] := by
  change co1BinaryAction monsterCo1GeometryVectorPoint109Transport monsterCo1GeometryBasePoint.val =
      _
  rw [monsterCo1GeometryVectorPoint109Transport_binary, monsterCo1GeometryBasePoint_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
