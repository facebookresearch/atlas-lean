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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint018
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint075

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The literal actual two-core word for source point 122. -/
def monsterCo1GeometryVectorPoint122Transport : Co1 :=
  monsterCo1GeometryVectorPoint18Transport * monsterCo1GeometryTransportOperator 6 *
    monsterCo1GeometryVectorPoint18Transport⁻¹ * monsterCo1GeometryVectorPoint75Transport

/-- Complete displayed binary matrix of actual transport 122. -/
def monsterCo1GeometryVectorPoint122Matrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![4299584, 8595993, 10702196, 9527097, 11955203, 3594595, 325710, 325838, 3598480,
      11987844, 8434452, 5495459, 10656800, 13777879, 6417136, 4222730, 502899, 5672935,
      7004857, 14383767, 6807558, 8908168, 5279590, 9642515]

/-- First complete finite matrix product in literal actual transport 122. -/
def monsterCo1GeometryVectorPoint122AfterSignMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![13060264, 14479063, 1862504, 10275544, 4344784, 4370353, 12742144, 12742353, 12766656,
      4377953, 8446992, 469751, 5033889, 14101054, 10962971, 3664749, 8646661, 9982000,
      13647777, 3994923, 1134965, 6699867, 5477075, 1106646]

/-- Second complete finite matrix product in literal actual transport 122. -/
def monsterCo1GeometryVectorPoint122AfterInverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![10379798, 14458388, 14457774, 6514218, 6062435, 14455885, 14907655, 14907847, 14907264,
      6063823, 4186961, 1997493, 15664420, 3003388, 11433971, 2280242, 12597262, 8504335,
      7013766, 12076358, 6112463, 15792142, 3320293, 9201176]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 24000000 in
-- Check every entry of this finite actual transport matrix in the Lean kernel.
/-- Every column of transport 122 is its actual Conway binary action. -/
theorem monsterCo1GeometryVectorPoint122Transport_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint122Transport v =
      monsterCo1GeometryVectorPoint122Matrix *ᵥ v := by
  have hx : monsterCo1GeometryVectorPoint18Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![12929074, 6220808, 10382183, 10406231, 12601423, 12627006, 12610767, 12610590, 12635279,
    12635182, 58368, 338093, 13552872, 13969570, 2443469, 3533053, 8646666, 1593978, 5389864,
    12384167, 9523772, 6568274, 5476570, 9495040] := by decide +kernel
  have hxi : monsterCo1GeometryVectorPoint18InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![2032, 13527770, 8255933, 7515289, 8394014, 58449, 8450703, 57505, 60906, 652, 4142659,
    4184467, 9814156, 4183730, 12566924, 12526973, 694056, 10637803, 378413, 9700495, 49792,
    18912, 8265921, 12579407] := by decide +kernel
  have hy : monsterCo1GeometryVectorPoint75Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![8446993, 8881459, 11003449, 2581646, 57504, 58400, 57456, 57584, 26272, 25408, 8389632,
    1183861, 8860884, 8414390, 10494444, 2138459, 5367925, 12917658, 13631434, 5995357,
    9478477, 9461761, 9825104, 8388784] := by rfl
  have he : monsterCo1GeometryVectorPoint122AfterSignMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![13060264, 14479063, 1862504, 10275544, 4344784, 4370353, 12742144, 12742353, 12766656,
    4377953, 8446992, 469751, 5033889, 14101054, 10962971, 3664749, 8646661, 9982000, 13647777,
    3994923, 1134965, 6699867, 5477075, 1106646] := by rfl
  have hf : monsterCo1GeometryVectorPoint122AfterInverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![10379798, 14458388, 14457774, 6514218, 6062435, 14455885, 14907655, 14907847, 14907264,
    6063823, 4186961, 1997493, 15664420, 3003388, 11433971, 2280242, 12597262, 8504335,
    7013766, 12076358, 6112463, 15792142, 3320293, 9201176] := by rfl
  have hc : monsterCo1GeometryVectorPoint122Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![4299584, 8595993, 10702196, 9527097, 11955203, 3594595, 325710, 325838, 3598480,
    11987844, 8434452, 5495459, 10656800, 13777879, 6417136, 4222730, 502899, 5672935, 7004857,
    14383767, 6807558, 8908168, 5279590, 9642515] := by rfl
  have hc1 : monsterCo1GeometryVectorPoint18Matrix *
    monsterCo1GeometryTransportOperatorMatrix 6 =
    monsterCo1GeometryVectorPoint122AfterSignMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![12929074, 6220808, 10382183, 10406231, 12601423, 12627006, 12610767, 12610590, 12635279,
    12635182, 58368, 338093, 13552872, 13969570, 2443469, 3533053, 8646666, 1593978, 5389864,
    12384167, 9523772, 6568274, 5476570, 9495040]
      (monsterCo1GeometryBinaryOperatorMasks 6)
    ![13060264, 14479063, 1862504, 10275544, 4344784, 4370353, 12742144, 12742353, 12766656,
    4377953, 8446992, 469751, 5033889, 14101054, 10962971, 3664749, 8646661, 9982000, 13647777,
    3994923, 1134965, 6699867, 5477075, 1106646] hx
    (monsterCo1GeometryBinaryOperatorMasks_decode 6) he (by decide +kernel)
  have hc2 : monsterCo1GeometryVectorPoint122AfterSignMatrix *
    monsterCo1GeometryVectorPoint18InverseMatrix =
    monsterCo1GeometryVectorPoint122AfterInverseMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![13060264, 14479063, 1862504, 10275544, 4344784, 4370353, 12742144, 12742353, 12766656,
    4377953, 8446992, 469751, 5033889, 14101054, 10962971, 3664749, 8646661, 9982000, 13647777,
    3994923, 1134965, 6699867, 5477075, 1106646]
    ![2032, 13527770, 8255933, 7515289, 8394014, 58449, 8450703, 57505, 60906, 652, 4142659,
    4184467, 9814156, 4183730, 12566924, 12526973, 694056, 10637803, 378413, 9700495, 49792,
    18912, 8265921, 12579407]
    ![10379798, 14458388, 14457774, 6514218, 6062435, 14455885, 14907655, 14907847, 14907264,
    6063823, 4186961, 1997493, 15664420, 3003388, 11433971, 2280242, 12597262, 8504335,
    7013766, 12076358, 6112463, 15792142, 3320293, 9201176] he hxi hf (by decide +kernel)
  have hc3 : monsterCo1GeometryVectorPoint122AfterInverseMatrix *
    monsterCo1GeometryVectorPoint75Matrix = monsterCo1GeometryVectorPoint122Matrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![10379798, 14458388, 14457774, 6514218, 6062435, 14455885, 14907655, 14907847, 14907264,
    6063823, 4186961, 1997493, 15664420, 3003388, 11433971, 2280242, 12597262, 8504335,
    7013766, 12076358, 6112463, 15792142, 3320293, 9201176]
    ![8446993, 8881459, 11003449, 2581646, 57504, 58400, 57456, 57584, 26272, 25408, 8389632,
    1183861, 8860884, 8414390, 10494444, 2138459, 5367925, 12917658, 13631434, 5995357,
    9478477, 9461761, 9825104, 8388784]
    ![4299584, 8595993, 10702196, 9527097, 11955203, 3594595, 325710, 325838, 3598480,
    11987844, 8434452, 5495459, 10656800, 13777879, 6417136, 4222730, 502899, 5672935, 7004857,
    14383767, 6807558, 8908168, 5279590, 9642515] hf hy hc (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_line_products
    monsterCo1GeometryVectorPoint18Transport monsterCo1GeometryVectorPoint75Transport 6
    monsterCo1GeometryVectorPoint18Matrix monsterCo1GeometryVectorPoint18InverseMatrix
    monsterCo1GeometryVectorPoint75Matrix
    monsterCo1GeometryVectorPoint122AfterSignMatrix
    monsterCo1GeometryVectorPoint122AfterInverseMatrix monsterCo1GeometryVectorPoint122Matrix
    monsterCo1GeometryVectorPoint18Transport_binary
    monsterCo1GeometryVectorPoint18Transport_inverse_binary
    monsterCo1GeometryVectorPoint75Transport_binary
    hc1 hc2 hc3 v

/-- Source point 122 is the literal actual transported frame point. -/
def monsterCo1GeometryVectorPoint122 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryVectorPoint122Transport • monsterCo1GeometryBasePoint

/-- Complete binary coordinates of this literal actual source point. -/
theorem monsterCo1GeometryVectorPoint122_binary :
    monsterCo1GeometryVectorPoint122.val =
      ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 0] := by
  change co1BinaryAction monsterCo1GeometryVectorPoint122Transport monsterCo1GeometryBasePoint.val =
      _
  rw [monsterCo1GeometryVectorPoint122Transport_binary, monsterCo1GeometryBasePoint_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
