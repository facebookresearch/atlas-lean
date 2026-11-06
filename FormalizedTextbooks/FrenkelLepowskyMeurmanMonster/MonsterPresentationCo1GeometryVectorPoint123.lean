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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint052
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint075

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The literal actual two-core word for source point 123. -/
def monsterCo1GeometryVectorPoint123Transport : Co1 :=
  monsterCo1GeometryVectorPoint52Transport * monsterCo1GeometryTransportOperator 6 *
    monsterCo1GeometryVectorPoint52Transport⁻¹ * monsterCo1GeometryVectorPoint75Transport

/-- Complete displayed binary matrix of actual transport 123. -/
def monsterCo1GeometryVectorPoint123Matrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![15973933, 9305547, 11859373, 8841184, 3717442, 12107142, 9055503, 9083947, 12073825,
      3706721, 8435108, 16289989, 11304610, 6303066, 4855698, 7053704, 9042806, 14072487,
      14988732, 5995575, 15303907, 592681, 13075592, 9639747]

/-- First complete finite matrix product in literal actual transport 123. -/
def monsterCo1GeometryVectorPoint123AfterSignMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![4681080, 6056135, 5112750, 13541918, 4344784, 12733345, 12742144, 4360897, 12766656,
      12724593, 8446992, 14018033, 13388209, 5705710, 7694093, 15058043, 8647733, 9982000,
      13688737, 3994923, 1135957, 6699867, 8489525, 1106646]

/-- Second complete finite matrix product in literal actual transport 123. -/
def monsterCo1GeometryVectorPoint123AfterInverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![10579773, 4806840, 833442, 11749926, 7778364, 4818511, 13191256, 7760837, 4817619,
      13210829, 12527453, 6593854, 8001418, 9621209, 15439656, 15154151, 13974018, 8515596,
      8259466, 3694923, 13129421, 5953887, 14831943, 9220634]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 24000000 in
-- Check every entry of this finite actual transport matrix in the Lean kernel.
/-- Every column of transport 123 is its actual Conway binary action. -/
theorem monsterCo1GeometryVectorPoint123Transport_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint123Transport v =
      monsterCo1GeometryVectorPoint123Matrix *ᵥ v := by
  have hx : monsterCo1GeometryVectorPoint52Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![12938418, 6187208, 13500840, 13542296, 12601423, 12601406, 12610767, 12617758, 12635279,
    12593198, 58368, 14018082, 13518888, 13962274, 7693890, 6669938, 259130, 1593978, 13819448,
    12384167, 1136156, 6568274, 8620261, 9495040] := by decide +kernel
  have hxi : monsterCo1GeometryVectorPoint52InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![1008, 14989972, 14105085, 14191832, 8394014, 58449, 8450703, 57505, 8399334, 652,
    12579407, 12573891, 1377408, 12522174, 4130176, 4186481, 693112, 10638587, 337452, 1373312,
    49792, 8423916, 13898206, 4142659] := by decide +kernel
  have hy : monsterCo1GeometryVectorPoint75Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![8446993, 8881459, 11003449, 2581646, 57504, 58400, 57456, 57584, 26272, 25408, 8389632,
    1183861, 8860884, 8414390, 10494444, 2138459, 5367925, 12917658, 13631434, 5995357,
    9478477, 9461761, 9825104, 8388784] := by rfl
  have he : monsterCo1GeometryVectorPoint123AfterSignMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![4681080, 6056135, 5112750, 13541918, 4344784, 12733345, 12742144, 4360897, 12766656,
    12724593, 8446992, 14018033, 13388209, 5705710, 7694093, 15058043, 8647733, 9982000,
    13688737, 3994923, 1135957, 6699867, 8489525, 1106646] := by rfl
  have hf : monsterCo1GeometryVectorPoint123AfterInverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![10579773, 4806840, 833442, 11749926, 7778364, 4818511, 13191256, 7760837, 4817619,
    13210829, 12527453, 6593854, 8001418, 9621209, 15439656, 15154151, 13974018, 8515596,
    8259466, 3694923, 13129421, 5953887, 14831943, 9220634] := by rfl
  have hc : monsterCo1GeometryVectorPoint123Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![15973933, 9305547, 11859373, 8841184, 3717442, 12107142, 9055503, 9083947, 12073825,
    3706721, 8435108, 16289989, 11304610, 6303066, 4855698, 7053704, 9042806, 14072487,
    14988732, 5995575, 15303907, 592681, 13075592, 9639747] := by rfl
  have hc1 : monsterCo1GeometryVectorPoint52Matrix *
    monsterCo1GeometryTransportOperatorMatrix 6 =
    monsterCo1GeometryVectorPoint123AfterSignMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![12938418, 6187208, 13500840, 13542296, 12601423, 12601406, 12610767, 12617758, 12635279,
    12593198, 58368, 14018082, 13518888, 13962274, 7693890, 6669938, 259130, 1593978, 13819448,
    12384167, 1136156, 6568274, 8620261, 9495040]
      (monsterCo1GeometryBinaryOperatorMasks 6)
    ![4681080, 6056135, 5112750, 13541918, 4344784, 12733345, 12742144, 4360897, 12766656,
    12724593, 8446992, 14018033, 13388209, 5705710, 7694093, 15058043, 8647733, 9982000,
    13688737, 3994923, 1135957, 6699867, 8489525, 1106646] hx
    (monsterCo1GeometryBinaryOperatorMasks_decode 6) he (by decide +kernel)
  have hc2 : monsterCo1GeometryVectorPoint123AfterSignMatrix *
    monsterCo1GeometryVectorPoint52InverseMatrix =
    monsterCo1GeometryVectorPoint123AfterInverseMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![4681080, 6056135, 5112750, 13541918, 4344784, 12733345, 12742144, 4360897, 12766656,
    12724593, 8446992, 14018033, 13388209, 5705710, 7694093, 15058043, 8647733, 9982000,
    13688737, 3994923, 1135957, 6699867, 8489525, 1106646]
    ![1008, 14989972, 14105085, 14191832, 8394014, 58449, 8450703, 57505, 8399334, 652,
    12579407, 12573891, 1377408, 12522174, 4130176, 4186481, 693112, 10638587, 337452, 1373312,
    49792, 8423916, 13898206, 4142659]
    ![10579773, 4806840, 833442, 11749926, 7778364, 4818511, 13191256, 7760837, 4817619,
    13210829, 12527453, 6593854, 8001418, 9621209, 15439656, 15154151, 13974018, 8515596,
    8259466, 3694923, 13129421, 5953887, 14831943, 9220634] he hxi hf (by decide +kernel)
  have hc3 : monsterCo1GeometryVectorPoint123AfterInverseMatrix *
    monsterCo1GeometryVectorPoint75Matrix = monsterCo1GeometryVectorPoint123Matrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![10579773, 4806840, 833442, 11749926, 7778364, 4818511, 13191256, 7760837, 4817619,
    13210829, 12527453, 6593854, 8001418, 9621209, 15439656, 15154151, 13974018, 8515596,
    8259466, 3694923, 13129421, 5953887, 14831943, 9220634]
    ![8446993, 8881459, 11003449, 2581646, 57504, 58400, 57456, 57584, 26272, 25408, 8389632,
    1183861, 8860884, 8414390, 10494444, 2138459, 5367925, 12917658, 13631434, 5995357,
    9478477, 9461761, 9825104, 8388784]
    ![15973933, 9305547, 11859373, 8841184, 3717442, 12107142, 9055503, 9083947, 12073825,
    3706721, 8435108, 16289989, 11304610, 6303066, 4855698, 7053704, 9042806, 14072487,
    14988732, 5995575, 15303907, 592681, 13075592, 9639747] hf hy hc (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_line_products
    monsterCo1GeometryVectorPoint52Transport monsterCo1GeometryVectorPoint75Transport 6
    monsterCo1GeometryVectorPoint52Matrix monsterCo1GeometryVectorPoint52InverseMatrix
    monsterCo1GeometryVectorPoint75Matrix
    monsterCo1GeometryVectorPoint123AfterSignMatrix
    monsterCo1GeometryVectorPoint123AfterInverseMatrix monsterCo1GeometryVectorPoint123Matrix
    monsterCo1GeometryVectorPoint52Transport_binary
    monsterCo1GeometryVectorPoint52Transport_inverse_binary
    monsterCo1GeometryVectorPoint75Transport_binary
    hc1 hc2 hc3 v

/-- Source point 123 is the literal actual transported frame point. -/
def monsterCo1GeometryVectorPoint123 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryVectorPoint123Transport • monsterCo1GeometryBasePoint

/-- Complete binary coordinates of this literal actual source point. -/
theorem monsterCo1GeometryVectorPoint123_binary :
    monsterCo1GeometryVectorPoint123.val =
      ![1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 0] := by
  change co1BinaryAction monsterCo1GeometryVectorPoint123Transport monsterCo1GeometryBasePoint.val =
      _
  rw [monsterCo1GeometryVectorPoint123Transport_binary, monsterCo1GeometryBasePoint_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
