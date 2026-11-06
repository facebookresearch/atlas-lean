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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint140
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint154

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The literal actual two-core word for source point 161. -/
def monsterCo1GeometryVectorPoint161Transport : Co1 :=
  monsterCo1GeometryVectorPoint140Transport * monsterCo1GeometryTransportOperator 1 *
    monsterCo1GeometryVectorPoint140Transport⁻¹ * monsterCo1GeometryVectorPoint154Transport

/-- Complete displayed binary matrix of actual transport 161. -/
def monsterCo1GeometryVectorPoint161Matrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![11585126, 218698, 14722938, 13891124, 10000835, 10992959, 2644904, 9927480, 1822470,
      1820696, 3364306, 7000405, 6418101, 16344378, 5847518, 6945769, 11307596, 14159988,
      814630, 131850, 15857735, 723164, 5925391, 4137150]

/-- First complete finite matrix product in literal actual transport 161. -/
def monsterCo1GeometryVectorPoint161AfterSignMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![49152, 1081345, 3187953, 2139217, 13678671, 5290046, 13662415, 5273630, 4250767,
      12639278, 1106944, 5301411, 9339078, 1426060, 10870147, 11919235, 6845936, 7574369,
      8173392, 6443489, 8467116, 316972, 9830030, 8445952]

/-- Second complete finite matrix product in literal actual transport 161. -/
def monsterCo1GeometryVectorPoint161AfterInverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![1, 12566542, 15769758, 15753326, 11150412, 9773168, 11150364, 9773264, 11199904, 9822892,
      8437760, 8381869, 8393170, 57437, 10874314, 10874166, 936395, 11701320, 756023, 12078101,
      9438301, 2097152, 9767340, 1276]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 24000000 in
-- Check every entry of this finite actual transport matrix in the Lean kernel.
/-- Every column of transport 161 is its actual Conway binary action. -/
theorem monsterCo1GeometryVectorPoint161Transport_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint161Transport v =
      monsterCo1GeometryVectorPoint161Matrix *ᵥ v := by
  have hx : monsterCo1GeometryVectorPoint140Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![49152, 1082881, 11577329, 10528081, 5286479, 5286462, 5270223, 5270046, 12635279,
    12635182, 9495040, 5300909, 951510, 1425580, 2477229, 3525805, 6845694, 7574623, 8172638,
    6444287, 79500, 316972, 1435808, 58368] := by rfl
  have hxi : monsterCo1GeometryVectorPoint140InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![1008, 13618512, 16522910, 15990383, 1326, 161, 1615, 81, 13591658, 49404, 12517616,
    7389184, 9822380, 4129009, 12518399, 12518398, 704753, 10634910, 377073, 9717151, 49152,
    13591296, 3206141, 4129804] := by rfl
  have hy : monsterCo1GeometryVectorPoint154Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![11585126, 12575234, 3195142, 8390493, 4129042, 8398589, 9421689, 11591930, 4178114,
    12567759, 1041033, 8913270, 6417940, 16446030, 7381098, 12842312, 2169949, 14029475,
    159522, 1021609, 13555816, 723164, 1881481, 8388848] := by rfl
  have he : monsterCo1GeometryVectorPoint161AfterSignMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![49152, 1081345, 3187953, 2139217, 13678671, 5290046, 13662415, 5273630, 4250767,
    12639278, 1106944, 5301411, 9339078, 1426060, 10870147, 11919235, 6845936, 7574369,
    8173392, 6443489, 8467116, 316972, 9830030, 8445952] := by rfl
  have hf : monsterCo1GeometryVectorPoint161AfterInverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![1, 12566542, 15769758, 15753326, 11150412, 9773168, 11150364, 9773264, 11199904, 9822892,
    8437760, 8381869, 8393170, 57437, 10874314, 10874166, 936395, 11701320, 756023, 12078101,
    9438301, 2097152, 9767340, 1276] := by rfl
  have hc : monsterCo1GeometryVectorPoint161Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![11585126, 218698, 14722938, 13891124, 10000835, 10992959, 2644904, 9927480, 1822470,
    1820696, 3364306, 7000405, 6418101, 16344378, 5847518, 6945769, 11307596, 14159988, 814630,
    131850, 15857735, 723164, 5925391, 4137150] := by rfl
  have hc1 : monsterCo1GeometryVectorPoint140Matrix *
    monsterCo1GeometryTransportOperatorMatrix 1 =
    monsterCo1GeometryVectorPoint161AfterSignMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![49152, 1082881, 11577329, 10528081, 5286479, 5286462, 5270223, 5270046, 12635279,
    12635182, 9495040, 5300909, 951510, 1425580, 2477229, 3525805, 6845694, 7574623, 8172638,
    6444287, 79500, 316972, 1435808, 58368]
      (monsterCo1GeometryBinaryOperatorMasks 1)
    ![49152, 1081345, 3187953, 2139217, 13678671, 5290046, 13662415, 5273630, 4250767,
    12639278, 1106944, 5301411, 9339078, 1426060, 10870147, 11919235, 6845936, 7574369,
    8173392, 6443489, 8467116, 316972, 9830030, 8445952] hx
    (monsterCo1GeometryBinaryOperatorMasks_decode 1) he (by decide +kernel)
  have hc2 : monsterCo1GeometryVectorPoint161AfterSignMatrix *
    monsterCo1GeometryVectorPoint140InverseMatrix =
    monsterCo1GeometryVectorPoint161AfterInverseMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![49152, 1081345, 3187953, 2139217, 13678671, 5290046, 13662415, 5273630, 4250767,
    12639278, 1106944, 5301411, 9339078, 1426060, 10870147, 11919235, 6845936, 7574369,
    8173392, 6443489, 8467116, 316972, 9830030, 8445952]
    ![1008, 13618512, 16522910, 15990383, 1326, 161, 1615, 81, 13591658, 49404, 12517616,
    7389184, 9822380, 4129009, 12518399, 12518398, 704753, 10634910, 377073, 9717151, 49152,
    13591296, 3206141, 4129804]
    ![1, 12566542, 15769758, 15753326, 11150412, 9773168, 11150364, 9773264, 11199904, 9822892,
    8437760, 8381869, 8393170, 57437, 10874314, 10874166, 936395, 11701320, 756023, 12078101,
    9438301, 2097152, 9767340, 1276] he hxi hf (by decide +kernel)
  have hc3 : monsterCo1GeometryVectorPoint161AfterInverseMatrix *
    monsterCo1GeometryVectorPoint154Matrix = monsterCo1GeometryVectorPoint161Matrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![1, 12566542, 15769758, 15753326, 11150412, 9773168, 11150364, 9773264, 11199904, 9822892,
    8437760, 8381869, 8393170, 57437, 10874314, 10874166, 936395, 11701320, 756023, 12078101,
    9438301, 2097152, 9767340, 1276]
    ![11585126, 12575234, 3195142, 8390493, 4129042, 8398589, 9421689, 11591930, 4178114,
    12567759, 1041033, 8913270, 6417940, 16446030, 7381098, 12842312, 2169949, 14029475,
    159522, 1021609, 13555816, 723164, 1881481, 8388848]
    ![11585126, 218698, 14722938, 13891124, 10000835, 10992959, 2644904, 9927480, 1822470,
    1820696, 3364306, 7000405, 6418101, 16344378, 5847518, 6945769, 11307596, 14159988, 814630,
    131850, 15857735, 723164, 5925391, 4137150] hf hy hc (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_line_products
    monsterCo1GeometryVectorPoint140Transport monsterCo1GeometryVectorPoint154Transport 1
    monsterCo1GeometryVectorPoint140Matrix monsterCo1GeometryVectorPoint140InverseMatrix
    monsterCo1GeometryVectorPoint154Matrix
    monsterCo1GeometryVectorPoint161AfterSignMatrix
    monsterCo1GeometryVectorPoint161AfterInverseMatrix monsterCo1GeometryVectorPoint161Matrix
    monsterCo1GeometryVectorPoint140Transport_binary
    monsterCo1GeometryVectorPoint140Transport_inverse_binary
    monsterCo1GeometryVectorPoint154Transport_binary
    hc1 hc2 hc3 v

/-- Source point 161 is the literal actual transported frame point. -/
def monsterCo1GeometryVectorPoint161 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryVectorPoint161Transport • monsterCo1GeometryBasePoint

/-- Complete binary coordinates of this literal actual source point. -/
theorem monsterCo1GeometryVectorPoint161_binary :
    monsterCo1GeometryVectorPoint161.val =
      ![0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0] := by
  change co1BinaryAction monsterCo1GeometryVectorPoint161Transport monsterCo1GeometryBasePoint.val =
      _
  rw [monsterCo1GeometryVectorPoint161Transport_binary, monsterCo1GeometryBasePoint_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
