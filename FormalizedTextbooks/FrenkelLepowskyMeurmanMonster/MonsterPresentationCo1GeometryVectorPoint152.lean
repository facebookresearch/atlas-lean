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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint022
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint136

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The literal actual two-core word for source point 152. -/
def monsterCo1GeometryVectorPoint152Transport : Co1 :=
  monsterCo1GeometryVectorPoint22Transport * monsterCo1GeometryTransportOperator 5 *
    monsterCo1GeometryVectorPoint22Transport⁻¹ * monsterCo1GeometryVectorPoint136Transport

/-- Complete displayed binary matrix of actual transport 152. -/
def monsterCo1GeometryVectorPoint152Matrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![8388689, 1887178, 8765553, 2557190, 16002373, 12583693, 6219782, 4194817, 5647038,
      6473514, 524648, 3870319, 11852167, 2148276, 11999661, 1564506, 7426198, 3701430,
      11752220, 10162692, 131205, 16614586, 13131505, 9044984]

/-- First complete finite matrix product in literal actual transport 152. -/
def monsterCo1GeometryVectorPoint152AfterSignMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![161, 12701184, 4522367, 12952207, 6253070, 1771519, 6262526, 10160015, 14675374, 1812095,
      18384, 8661006, 5356396, 9496221, 7582931, 6534751, 5871835, 5054251, 4339791, 10671429,
      18187, 11550848, 13865753, 1106604]

/-- Second complete finite matrix product in literal actual transport 152. -/
def monsterCo1GeometryVectorPoint152AfterInverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![1, 9260303, 15771108, 15747998, 2893151, 12845957, 1253827, 5317460, 2935881, 5361570,
      11194059, 4383777, 14103078, 6661089, 778889, 5350820, 625408, 10502603, 6112930,
      6736238, 3140282, 6981975, 15818824, 7381904]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 24000000 in
-- Check every entry of this finite actual transport matrix in the Lean kernel.
/-- Every column of transport 152 is its actual Conway binary action. -/
theorem monsterCo1GeometryVectorPoint152Transport_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint152Transport v =
      monsterCo1GeometryVectorPoint152Matrix *ᵥ v := by
  have hx : monsterCo1GeometryVectorPoint22Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![161, 12635279, 12911475, 12951875, 6187208, 10159226, 6196248, 10159114, 6220808,
    10200122, 17968, 338093, 13679119, 9496113, 7583098, 6535034, 14194718, 13377038, 4405967,
    2283296, 8406763, 3162406, 5476570, 9495040] := by decide +kernel
  have hxi : monsterCo1GeometryVectorPoint22InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![1277, 11634767, 5319554, 3452063, 11191372, 4129996, 9814048, 4128816, 4132375, 652,
    1434749, 2812211, 8450371, 2811773, 8397425, 12526973, 6702110, 14832526, 247116, 8467776,
    49804, 4213227, 8266158, 9773169] := by decide +kernel
  have hy : monsterCo1GeometryVectorPoint136Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![8388689, 4137102, 9421685, 983705, 4186735, 8397216, 12576307, 8397296, 12574979,
    8446016, 8439216, 3680048, 1439007, 11191776, 14154011, 14154919, 15892019, 3379403,
    13785811, 5502065, 705793, 6260699, 2276025, 8388848] := by rfl
  have he : monsterCo1GeometryVectorPoint152AfterSignMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![161, 12701184, 4522367, 12952207, 6253070, 1771519, 6262526, 10160015, 14675374, 1812095,
    18384, 8661006, 5356396, 9496221, 7582931, 6534751, 5871835, 5054251, 4339791, 10671429,
    18187, 11550848, 13865753, 1106604] := by rfl
  have hf : monsterCo1GeometryVectorPoint152AfterInverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![1, 9260303, 15771108, 15747998, 2893151, 12845957, 1253827, 5317460, 2935881, 5361570,
    11194059, 4383777, 14103078, 6661089, 778889, 5350820, 625408, 10502603, 6112930, 6736238,
    3140282, 6981975, 15818824, 7381904] := by rfl
  have hc : monsterCo1GeometryVectorPoint152Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![8388689, 1887178, 8765553, 2557190, 16002373, 12583693, 6219782, 4194817, 5647038,
    6473514, 524648, 3870319, 11852167, 2148276, 11999661, 1564506, 7426198, 3701430, 11752220,
    10162692, 131205, 16614586, 13131505, 9044984] := by rfl
  have hc1 : monsterCo1GeometryVectorPoint22Matrix *
    monsterCo1GeometryTransportOperatorMatrix 5 =
    monsterCo1GeometryVectorPoint152AfterSignMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![161, 12635279, 12911475, 12951875, 6187208, 10159226, 6196248, 10159114, 6220808,
    10200122, 17968, 338093, 13679119, 9496113, 7583098, 6535034, 14194718, 13377038, 4405967,
    2283296, 8406763, 3162406, 5476570, 9495040]
      (monsterCo1GeometryBinaryOperatorMasks 5)
    ![161, 12701184, 4522367, 12952207, 6253070, 1771519, 6262526, 10160015, 14675374, 1812095,
    18384, 8661006, 5356396, 9496221, 7582931, 6534751, 5871835, 5054251, 4339791, 10671429,
    18187, 11550848, 13865753, 1106604] hx (monsterCo1GeometryBinaryOperatorMasks_decode 5) he
    (by decide +kernel)
  have hc2 : monsterCo1GeometryVectorPoint152AfterSignMatrix *
    monsterCo1GeometryVectorPoint22InverseMatrix =
    monsterCo1GeometryVectorPoint152AfterInverseMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![161, 12701184, 4522367, 12952207, 6253070, 1771519, 6262526, 10160015, 14675374, 1812095,
    18384, 8661006, 5356396, 9496221, 7582931, 6534751, 5871835, 5054251, 4339791, 10671429,
    18187, 11550848, 13865753, 1106604]
    ![1277, 11634767, 5319554, 3452063, 11191372, 4129996, 9814048, 4128816, 4132375, 652,
    1434749, 2812211, 8450371, 2811773, 8397425, 12526973, 6702110, 14832526, 247116, 8467776,
    49804, 4213227, 8266158, 9773169]
    ![1, 9260303, 15771108, 15747998, 2893151, 12845957, 1253827, 5317460, 2935881, 5361570,
    11194059, 4383777, 14103078, 6661089, 778889, 5350820, 625408, 10502603, 6112930, 6736238,
    3140282, 6981975, 15818824, 7381904] he hxi hf (by decide +kernel)
  have hc3 : monsterCo1GeometryVectorPoint152AfterInverseMatrix *
    monsterCo1GeometryVectorPoint136Matrix = monsterCo1GeometryVectorPoint152Matrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![1, 9260303, 15771108, 15747998, 2893151, 12845957, 1253827, 5317460, 2935881, 5361570,
    11194059, 4383777, 14103078, 6661089, 778889, 5350820, 625408, 10502603, 6112930, 6736238,
    3140282, 6981975, 15818824, 7381904]
    ![8388689, 4137102, 9421685, 983705, 4186735, 8397216, 12576307, 8397296, 12574979,
    8446016, 8439216, 3680048, 1439007, 11191776, 14154011, 14154919, 15892019, 3379403,
    13785811, 5502065, 705793, 6260699, 2276025, 8388848]
    ![8388689, 1887178, 8765553, 2557190, 16002373, 12583693, 6219782, 4194817, 5647038,
    6473514, 524648, 3870319, 11852167, 2148276, 11999661, 1564506, 7426198, 3701430, 11752220,
    10162692, 131205, 16614586, 13131505, 9044984] hf hy hc (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_line_products
    monsterCo1GeometryVectorPoint22Transport monsterCo1GeometryVectorPoint136Transport 5
    monsterCo1GeometryVectorPoint22Matrix monsterCo1GeometryVectorPoint22InverseMatrix
    monsterCo1GeometryVectorPoint136Matrix
    monsterCo1GeometryVectorPoint152AfterSignMatrix
    monsterCo1GeometryVectorPoint152AfterInverseMatrix monsterCo1GeometryVectorPoint152Matrix
    monsterCo1GeometryVectorPoint22Transport_binary
    monsterCo1GeometryVectorPoint22Transport_inverse_binary
    monsterCo1GeometryVectorPoint136Transport_binary
    hc1 hc2 hc3 v

/-- Source point 152 is the literal actual transported frame point. -/
def monsterCo1GeometryVectorPoint152 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryVectorPoint152Transport • monsterCo1GeometryBasePoint

/-- Complete binary coordinates of this literal actual source point. -/
theorem monsterCo1GeometryVectorPoint152_binary :
    monsterCo1GeometryVectorPoint152.val =
      ![0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 0] := by
  change co1BinaryAction monsterCo1GeometryVectorPoint152Transport monsterCo1GeometryBasePoint.val =
      _
  rw [monsterCo1GeometryVectorPoint152Transport_binary, monsterCo1GeometryBasePoint_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
