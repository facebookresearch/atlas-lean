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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint100

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The literal actual two-core word for source point 143. -/
def monsterCo1GeometryVectorPoint143Transport : Co1 :=
  monsterCo1GeometryVectorPoint22Transport * monsterCo1GeometryTransportOperator 6 *
    monsterCo1GeometryVectorPoint22Transport⁻¹ * monsterCo1GeometryVectorPoint100Transport

/-- Complete displayed binary matrix of actual transport 143. -/
def monsterCo1GeometryVectorPoint143Matrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![8389280, 3177012, 5998239, 2885093, 4816776, 15921936, 13082104, 15922545, 13237081,
      8745068, 16343514, 1187542, 11114965, 1073650, 11193091, 12234658, 16180360, 1787552,
      14939448, 14719230, 6808405, 3318023, 9834464, 2000486]

/-- First complete finite matrix product in literal actual transport 143. -/
def monsterCo1GeometryVectorPoint143AfterSignMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![8388769, 12766656, 4522102, 12952006, 6056135, 1770943, 14453767, 10159567, 14479063,
      1812095, 17824, 469751, 5421398, 9496295, 7583343, 6534313, 14326555, 5118999, 4275087,
      2283068, 8406395, 3162684, 5477075, 1106646]

/-- Second complete finite matrix product in literal actual transport 143. -/
def monsterCo1GeometryVectorPoint143AfterInverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![9773168, 10262036, 16450449, 7221063, 3561521, 5357865, 638044, 12902904, 10715008,
      5361570, 11193575, 5798334, 4440938, 14714769, 12887976, 9307253, 9269354, 15408477,
      5021113, 16272710, 12241127, 3206151, 7645934, 16091104]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 24000000 in
-- Check every entry of this finite actual transport matrix in the Lean kernel.
/-- Every column of transport 143 is its actual Conway binary action. -/
theorem monsterCo1GeometryVectorPoint143Transport_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint143Transport v =
      monsterCo1GeometryVectorPoint143Matrix *ᵥ v := by
  have hx : monsterCo1GeometryVectorPoint22Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![161, 12635279, 12911475, 12951875, 6187208, 10159226, 6196248, 10159114, 6220808,
    10200122, 17968, 338093, 13679119, 9496113, 7583098, 6535034, 14194718, 13377038, 4405967,
    2283296, 8406763, 3162406, 5476570, 9495040] := by decide +kernel
  have hxi : monsterCo1GeometryVectorPoint22InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![1277, 11634767, 5319554, 3452063, 11191372, 4129996, 9814048, 4128816, 4132375, 652,
    1434749, 2812211, 8450371, 2811773, 8397425, 12526973, 6702110, 14832526, 247116, 8467776,
    49804, 4213227, 8266158, 9773169] := by decide +kernel
  have hy : monsterCo1GeometryVectorPoint100Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![1041, 513571, 11006574, 2585529, 8860658, 8414096, 472565, 25408, 8894245, 8447216,
    34560, 14099015, 938853, 9364885, 5790597, 5790085, 13708597, 4549757, 4304552, 1670447,
    10356111, 5621254, 10320567, 1200] := by rfl
  have he : monsterCo1GeometryVectorPoint143AfterSignMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![8388769, 12766656, 4522102, 12952006, 6056135, 1770943, 14453767, 10159567, 14479063,
    1812095, 17824, 469751, 5421398, 9496295, 7583343, 6534313, 14326555, 5118999, 4275087,
    2283068, 8406395, 3162684, 5477075, 1106646] := by rfl
  have hf : monsterCo1GeometryVectorPoint143AfterInverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![9773168, 10262036, 16450449, 7221063, 3561521, 5357865, 638044, 12902904, 10715008,
    5361570, 11193575, 5798334, 4440938, 14714769, 12887976, 9307253, 9269354, 15408477,
    5021113, 16272710, 12241127, 3206151, 7645934, 16091104] := by rfl
  have hc : monsterCo1GeometryVectorPoint143Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![8389280, 3177012, 5998239, 2885093, 4816776, 15921936, 13082104, 15922545, 13237081,
    8745068, 16343514, 1187542, 11114965, 1073650, 11193091, 12234658, 16180360, 1787552,
    14939448, 14719230, 6808405, 3318023, 9834464, 2000486] := by rfl
  have hc1 : monsterCo1GeometryVectorPoint22Matrix *
    monsterCo1GeometryTransportOperatorMatrix 6 =
    monsterCo1GeometryVectorPoint143AfterSignMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![161, 12635279, 12911475, 12951875, 6187208, 10159226, 6196248, 10159114, 6220808,
    10200122, 17968, 338093, 13679119, 9496113, 7583098, 6535034, 14194718, 13377038, 4405967,
    2283296, 8406763, 3162406, 5476570, 9495040]
      (monsterCo1GeometryBinaryOperatorMasks 6)
    ![8388769, 12766656, 4522102, 12952006, 6056135, 1770943, 14453767, 10159567, 14479063,
    1812095, 17824, 469751, 5421398, 9496295, 7583343, 6534313, 14326555, 5118999, 4275087,
    2283068, 8406395, 3162684, 5477075, 1106646] hx
    (monsterCo1GeometryBinaryOperatorMasks_decode 6) he (by decide +kernel)
  have hc2 : monsterCo1GeometryVectorPoint143AfterSignMatrix *
    monsterCo1GeometryVectorPoint22InverseMatrix =
    monsterCo1GeometryVectorPoint143AfterInverseMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![8388769, 12766656, 4522102, 12952006, 6056135, 1770943, 14453767, 10159567, 14479063,
    1812095, 17824, 469751, 5421398, 9496295, 7583343, 6534313, 14326555, 5118999, 4275087,
    2283068, 8406395, 3162684, 5477075, 1106646]
    ![1277, 11634767, 5319554, 3452063, 11191372, 4129996, 9814048, 4128816, 4132375, 652,
    1434749, 2812211, 8450371, 2811773, 8397425, 12526973, 6702110, 14832526, 247116, 8467776,
    49804, 4213227, 8266158, 9773169]
    ![9773168, 10262036, 16450449, 7221063, 3561521, 5357865, 638044, 12902904, 10715008,
    5361570, 11193575, 5798334, 4440938, 14714769, 12887976, 9307253, 9269354, 15408477,
    5021113, 16272710, 12241127, 3206151, 7645934, 16091104] he hxi hf (by decide +kernel)
  have hc3 : monsterCo1GeometryVectorPoint143AfterInverseMatrix *
    monsterCo1GeometryVectorPoint100Matrix = monsterCo1GeometryVectorPoint143Matrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![9773168, 10262036, 16450449, 7221063, 3561521, 5357865, 638044, 12902904, 10715008,
    5361570, 11193575, 5798334, 4440938, 14714769, 12887976, 9307253, 9269354, 15408477,
    5021113, 16272710, 12241127, 3206151, 7645934, 16091104]
    ![1041, 513571, 11006574, 2585529, 8860658, 8414096, 472565, 25408, 8894245, 8447216,
    34560, 14099015, 938853, 9364885, 5790597, 5790085, 13708597, 4549757, 4304552, 1670447,
    10356111, 5621254, 10320567, 1200]
    ![8389280, 3177012, 5998239, 2885093, 4816776, 15921936, 13082104, 15922545, 13237081,
    8745068, 16343514, 1187542, 11114965, 1073650, 11193091, 12234658, 16180360, 1787552,
    14939448, 14719230, 6808405, 3318023, 9834464, 2000486] hf hy hc (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_line_products
    monsterCo1GeometryVectorPoint22Transport monsterCo1GeometryVectorPoint100Transport 6
    monsterCo1GeometryVectorPoint22Matrix monsterCo1GeometryVectorPoint22InverseMatrix
    monsterCo1GeometryVectorPoint100Matrix
    monsterCo1GeometryVectorPoint143AfterSignMatrix
    monsterCo1GeometryVectorPoint143AfterInverseMatrix monsterCo1GeometryVectorPoint143Matrix
    monsterCo1GeometryVectorPoint22Transport_binary
    monsterCo1GeometryVectorPoint22Transport_inverse_binary
    monsterCo1GeometryVectorPoint100Transport_binary
    hc1 hc2 hc3 v

/-- Source point 143 is the literal actual transported frame point. -/
def monsterCo1GeometryVectorPoint143 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryVectorPoint143Transport • monsterCo1GeometryBasePoint

/-- Complete binary coordinates of this literal actual source point. -/
theorem monsterCo1GeometryVectorPoint143_binary :
    monsterCo1GeometryVectorPoint143.val =
      ![0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 1, 0, 0, 1, 0] := by
  change co1BinaryAction monsterCo1GeometryVectorPoint143Transport monsterCo1GeometryBasePoint.val =
      _
  rw [monsterCo1GeometryVectorPoint143Transport_binary, monsterCo1GeometryBasePoint_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
