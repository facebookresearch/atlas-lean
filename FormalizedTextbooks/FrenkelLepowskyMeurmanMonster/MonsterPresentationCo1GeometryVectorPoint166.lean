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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint146
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint156

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The literal actual two-core word for source point 166. -/
def monsterCo1GeometryVectorPoint166Transport : Co1 :=
  monsterCo1GeometryVectorPoint146Transport * monsterCo1GeometryTransportOperator 1 *
    monsterCo1GeometryVectorPoint146Transport⁻¹ * monsterCo1GeometryVectorPoint156Transport

/-- Complete displayed binary matrix of actual transport 166. -/
def monsterCo1GeometryVectorPoint166Matrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![3204107, 9380612, 12, 992245, 983641, 983560, 8447152, 4187843, 8397405, 8541, 11543990,
      7467978, 16065819, 5373663, 8413638, 13383324, 5368025, 13223262, 7391127, 386532,
      1098023, 8243405, 7390815, 8388848]

/-- First complete finite matrix product in literal actual transport 166. -/
def monsterCo1GeometryVectorPoint166AfterSignMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![8900804, 513714, 1152, 11006799, 2593720, 2147836, 10948985, 10949113, 10502603, 2115133,
      11006232, 8812307, 3390589, 1564489, 4290558, 198325, 10762877, 23986, 6004848, 8109360,
      9686312, 9495249, 8586054, 1200]

/-- Second complete finite matrix product in literal actual transport 166. -/
def monsterCo1GeometryVectorPoint166AfterInverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![8388613, 8388614, 4, 8389387, 8389280, 995, 8389172, 8389364, 519, 263, 8390320, 5094524,
      3314382, 3318029, 12351483, 8421815, 13370156, 13566300, 9044645, 4915533, 2261182,
      6258773, 12582916, 8388608]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 24000000 in
-- Check every entry of this finite actual transport matrix in the Lean kernel.
/-- Every column of transport 166 is its actual Conway binary action. -/
theorem monsterCo1GeometryVectorPoint166Transport_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint166Transport v =
      monsterCo1GeometryVectorPoint166Matrix *ᵥ v := by
  have hx : monsterCo1GeometryVectorPoint146Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![8900852, 513666, 1152, 11007615, 10983048, 2147580, 2560073, 2560201, 10503371, 2114365,
    2618408, 423683, 11775811, 9948535, 4290512, 8586885, 10760051, 8407484, 6005326, 8105472,
    9690902, 9495761, 8586102, 1200] := by rfl
  have hxi : monsterCo1GeometryVectorPoint146InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![13480196, 12616405, 15905574, 4436931, 5092815, 13481419, 13479954, 192, 963, 8355985,
    196, 1152827, 12354075, 9479507, 2266474, 8355936, 2268982, 6462514, 2004567, 1800748,
    10487095, 10593757, 13888415, 435] := by rfl
  have hy : monsterCo1GeometryVectorPoint156Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![11592951, 992248, 12, 11593482, 11584870, 9421940, 8397296, 4137859, 12576350, 4187486,
    1041033, 7532745, 10681568, 8839512, 8605957, 4994464, 378413, 1912342, 4981211, 13766435,
    13098336, 16661758, 15779491, 8388848] := by rfl
  have he : monsterCo1GeometryVectorPoint166AfterSignMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![8900804, 513714, 1152, 11006799, 2593720, 2147836, 10948985, 10949113, 10502603, 2115133,
    11006232, 8812307, 3390589, 1564489, 4290558, 198325, 10762877, 23986, 6004848, 8109360,
    9686312, 9495249, 8586054, 1200] := by rfl
  have hf : monsterCo1GeometryVectorPoint166AfterInverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![8388613, 8388614, 4, 8389387, 8389280, 995, 8389172, 8389364, 519, 263, 8390320, 5094524,
    3314382, 3318029, 12351483, 8421815, 13370156, 13566300, 9044645, 4915533, 2261182,
    6258773, 12582916, 8388608] := by rfl
  have hc : monsterCo1GeometryVectorPoint166Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![3204107, 9380612, 12, 992245, 983641, 983560, 8447152, 4187843, 8397405, 8541, 11543990,
    7467978, 16065819, 5373663, 8413638, 13383324, 5368025, 13223262, 7391127, 386532, 1098023,
    8243405, 7390815, 8388848] := by rfl
  have hc1 : monsterCo1GeometryVectorPoint146Matrix *
    monsterCo1GeometryTransportOperatorMatrix 1 =
    monsterCo1GeometryVectorPoint166AfterSignMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![8900852, 513666, 1152, 11007615, 10983048, 2147580, 2560073, 2560201, 10503371, 2114365,
    2618408, 423683, 11775811, 9948535, 4290512, 8586885, 10760051, 8407484, 6005326, 8105472,
    9690902, 9495761, 8586102, 1200]
      (monsterCo1GeometryBinaryOperatorMasks 1)
    ![8900804, 513714, 1152, 11006799, 2593720, 2147836, 10948985, 10949113, 10502603, 2115133,
    11006232, 8812307, 3390589, 1564489, 4290558, 198325, 10762877, 23986, 6004848, 8109360,
    9686312, 9495249, 8586054, 1200] hx (monsterCo1GeometryBinaryOperatorMasks_decode 1) he (by
    decide +kernel)
  have hc2 : monsterCo1GeometryVectorPoint166AfterSignMatrix *
    monsterCo1GeometryVectorPoint146InverseMatrix =
    monsterCo1GeometryVectorPoint166AfterInverseMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![8900804, 513714, 1152, 11006799, 2593720, 2147836, 10948985, 10949113, 10502603, 2115133,
    11006232, 8812307, 3390589, 1564489, 4290558, 198325, 10762877, 23986, 6004848, 8109360,
    9686312, 9495249, 8586054, 1200]
    ![13480196, 12616405, 15905574, 4436931, 5092815, 13481419, 13479954, 192, 963, 8355985,
    196, 1152827, 12354075, 9479507, 2266474, 8355936, 2268982, 6462514, 2004567, 1800748,
    10487095, 10593757, 13888415, 435]
    ![8388613, 8388614, 4, 8389387, 8389280, 995, 8389172, 8389364, 519, 263, 8390320, 5094524,
    3314382, 3318029, 12351483, 8421815, 13370156, 13566300, 9044645, 4915533, 2261182,
    6258773, 12582916, 8388608] he hxi hf (by decide +kernel)
  have hc3 : monsterCo1GeometryVectorPoint166AfterInverseMatrix *
    monsterCo1GeometryVectorPoint156Matrix = monsterCo1GeometryVectorPoint166Matrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![8388613, 8388614, 4, 8389387, 8389280, 995, 8389172, 8389364, 519, 263, 8390320, 5094524,
    3314382, 3318029, 12351483, 8421815, 13370156, 13566300, 9044645, 4915533, 2261182,
    6258773, 12582916, 8388608]
    ![11592951, 992248, 12, 11593482, 11584870, 9421940, 8397296, 4137859, 12576350, 4187486,
    1041033, 7532745, 10681568, 8839512, 8605957, 4994464, 378413, 1912342, 4981211, 13766435,
    13098336, 16661758, 15779491, 8388848]
    ![3204107, 9380612, 12, 992245, 983641, 983560, 8447152, 4187843, 8397405, 8541, 11543990,
    7467978, 16065819, 5373663, 8413638, 13383324, 5368025, 13223262, 7391127, 386532, 1098023,
    8243405, 7390815, 8388848] hf hy hc (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_line_products
    monsterCo1GeometryVectorPoint146Transport monsterCo1GeometryVectorPoint156Transport 1
    monsterCo1GeometryVectorPoint146Matrix monsterCo1GeometryVectorPoint146InverseMatrix
    monsterCo1GeometryVectorPoint156Matrix
    monsterCo1GeometryVectorPoint166AfterSignMatrix
    monsterCo1GeometryVectorPoint166AfterInverseMatrix monsterCo1GeometryVectorPoint166Matrix
    monsterCo1GeometryVectorPoint146Transport_binary
    monsterCo1GeometryVectorPoint146Transport_inverse_binary
    monsterCo1GeometryVectorPoint156Transport_binary
    hc1 hc2 hc3 v

/-- Source point 166 is the literal actual transported frame point. -/
def monsterCo1GeometryVectorPoint166 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryVectorPoint166Transport • monsterCo1GeometryBasePoint

/-- Complete binary coordinates of this literal actual source point. -/
theorem monsterCo1GeometryVectorPoint166_binary :
    monsterCo1GeometryVectorPoint166.val =
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0] := by
  change co1BinaryAction monsterCo1GeometryVectorPoint166Transport monsterCo1GeometryBasePoint.val =
      _
  rw [monsterCo1GeometryVectorPoint166Transport_binary, monsterCo1GeometryBasePoint_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
