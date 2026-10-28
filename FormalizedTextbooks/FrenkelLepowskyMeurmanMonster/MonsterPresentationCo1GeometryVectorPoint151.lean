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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint129

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The literal actual two-core word for source point 151. -/
def monsterCo1GeometryVectorPoint151Transport : Co1 :=
  monsterCo1GeometryVectorPoint22Transport * monsterCo1GeometryTransportOperator 5 *
    monsterCo1GeometryVectorPoint22Transport⁻¹ * monsterCo1GeometryVectorPoint129Transport

/-- Complete displayed binary matrix of actual transport 151. -/
def monsterCo1GeometryVectorPoint151Matrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![1089, 14293486, 13128390, 13211440, 14923957, 5247586, 16158007, 13636673, 6471487,
      13750555, 9761563, 8830865, 831019, 4355916, 10957801, 15758822, 14187973, 1057292,
      634410, 11886490, 9761603, 13026179, 14741738, 4354658]

/-- First complete finite matrix product in literal actual transport 151. -/
def monsterCo1GeometryVectorPoint151AfterSignMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![161, 12701184, 4522367, 12952207, 6253070, 1771519, 6262526, 10160015, 14675374, 1812095,
      18384, 8661006, 5356396, 9496221, 7582931, 6534751, 5871835, 5054251, 4339791, 10671429,
      18187, 11550848, 13865753, 1106604]

/-- Second complete finite matrix product in literal actual transport 151. -/
def monsterCo1GeometryVectorPoint151AfterInverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![1, 9260303, 15771108, 15747998, 2893151, 12845957, 1253827, 5317460, 2935881, 5361570,
      11194059, 4383777, 14103078, 6661089, 778889, 5350820, 625408, 10502603, 6112930,
      6736238, 3140282, 6981975, 15818824, 7381904]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 24000000 in
-- Check every entry of this finite actual transport matrix in the Lean kernel.
/-- Every column of transport 151 is its actual Conway binary action. -/
theorem monsterCo1GeometryVectorPoint151Transport_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint151Transport v =
      monsterCo1GeometryVectorPoint151Matrix *ᵥ v := by
  have hx : monsterCo1GeometryVectorPoint22Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![161, 12635279, 12911475, 12951875, 6187208, 10159226, 6196248, 10159114, 6220808,
    10200122, 17968, 338093, 13679119, 9496113, 7583098, 6535034, 14194718, 13377038, 4405967,
    2283296, 8406763, 3162406, 5476570, 9495040] := by decide +kernel
  have hxi : monsterCo1GeometryVectorPoint22InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![1277, 11634767, 5319554, 3452063, 11191372, 4129996, 9814048, 4128816, 4132375, 652,
    1434749, 2812211, 8450371, 2811773, 8397425, 12526973, 6702110, 14832526, 247116, 8467776,
    49804, 4213227, 8266158, 9773169] := by decide +kernel
  have hy : monsterCo1GeometryVectorPoint129Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![1089, 2811410, 664852, 9052408, 58496, 64, 8445984, 8388672, 9968, 1280, 8389632,
    2164381, 2806046, 8389469, 10512187, 10511367, 11044364, 7614174, 11043320, 15841955,
    8389243, 9453916, 15896879, 8388688] := by rfl
  have he : monsterCo1GeometryVectorPoint151AfterSignMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![161, 12701184, 4522367, 12952207, 6253070, 1771519, 6262526, 10160015, 14675374, 1812095,
    18384, 8661006, 5356396, 9496221, 7582931, 6534751, 5871835, 5054251, 4339791, 10671429,
    18187, 11550848, 13865753, 1106604] := by rfl
  have hf : monsterCo1GeometryVectorPoint151AfterInverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![1, 9260303, 15771108, 15747998, 2893151, 12845957, 1253827, 5317460, 2935881, 5361570,
    11194059, 4383777, 14103078, 6661089, 778889, 5350820, 625408, 10502603, 6112930, 6736238,
    3140282, 6981975, 15818824, 7381904] := by rfl
  have hc : monsterCo1GeometryVectorPoint151Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![1089, 14293486, 13128390, 13211440, 14923957, 5247586, 16158007, 13636673, 6471487,
    13750555, 9761563, 8830865, 831019, 4355916, 10957801, 15758822, 14187973, 1057292, 634410,
    11886490, 9761603, 13026179, 14741738, 4354658] := by rfl
  have hc1 : monsterCo1GeometryVectorPoint22Matrix *
    monsterCo1GeometryTransportOperatorMatrix 5 =
    monsterCo1GeometryVectorPoint151AfterSignMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![161, 12635279, 12911475, 12951875, 6187208, 10159226, 6196248, 10159114, 6220808,
    10200122, 17968, 338093, 13679119, 9496113, 7583098, 6535034, 14194718, 13377038, 4405967,
    2283296, 8406763, 3162406, 5476570, 9495040]
      (monsterCo1GeometryBinaryOperatorMasks 5)
    ![161, 12701184, 4522367, 12952207, 6253070, 1771519, 6262526, 10160015, 14675374, 1812095,
    18384, 8661006, 5356396, 9496221, 7582931, 6534751, 5871835, 5054251, 4339791, 10671429,
    18187, 11550848, 13865753, 1106604] hx (monsterCo1GeometryBinaryOperatorMasks_decode 5) he
    (by decide +kernel)
  have hc2 : monsterCo1GeometryVectorPoint151AfterSignMatrix *
    monsterCo1GeometryVectorPoint22InverseMatrix =
    monsterCo1GeometryVectorPoint151AfterInverseMatrix :=
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
  have hc3 : monsterCo1GeometryVectorPoint151AfterInverseMatrix *
    monsterCo1GeometryVectorPoint129Matrix = monsterCo1GeometryVectorPoint151Matrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![1, 9260303, 15771108, 15747998, 2893151, 12845957, 1253827, 5317460, 2935881, 5361570,
    11194059, 4383777, 14103078, 6661089, 778889, 5350820, 625408, 10502603, 6112930, 6736238,
    3140282, 6981975, 15818824, 7381904]
    ![1089, 2811410, 664852, 9052408, 58496, 64, 8445984, 8388672, 9968, 1280, 8389632,
    2164381, 2806046, 8389469, 10512187, 10511367, 11044364, 7614174, 11043320, 15841955,
    8389243, 9453916, 15896879, 8388688]
    ![1089, 14293486, 13128390, 13211440, 14923957, 5247586, 16158007, 13636673, 6471487,
    13750555, 9761563, 8830865, 831019, 4355916, 10957801, 15758822, 14187973, 1057292, 634410,
    11886490, 9761603, 13026179, 14741738, 4354658] hf hy hc (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_line_products
    monsterCo1GeometryVectorPoint22Transport monsterCo1GeometryVectorPoint129Transport 5
    monsterCo1GeometryVectorPoint22Matrix monsterCo1GeometryVectorPoint22InverseMatrix
    monsterCo1GeometryVectorPoint129Matrix
    monsterCo1GeometryVectorPoint151AfterSignMatrix
    monsterCo1GeometryVectorPoint151AfterInverseMatrix monsterCo1GeometryVectorPoint151Matrix
    monsterCo1GeometryVectorPoint22Transport_binary
    monsterCo1GeometryVectorPoint22Transport_inverse_binary
    monsterCo1GeometryVectorPoint129Transport_binary
    hc1 hc2 hc3 v

/-- Source point 151 is the literal actual transported frame point. -/
def monsterCo1GeometryVectorPoint151 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryVectorPoint151Transport • monsterCo1GeometryBasePoint

/-- Complete binary coordinates of this literal actual source point. -/
theorem monsterCo1GeometryVectorPoint151_binary :
    monsterCo1GeometryVectorPoint151.val =
      ![0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0] := by
  change co1BinaryAction monsterCo1GeometryVectorPoint151Transport monsterCo1GeometryBasePoint.val =
      _
  rw [monsterCo1GeometryVectorPoint151Transport_binary, monsterCo1GeometryBasePoint_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
