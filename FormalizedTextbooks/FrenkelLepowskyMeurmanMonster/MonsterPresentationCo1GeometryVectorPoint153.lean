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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint110
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint136

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The literal actual two-core word for source point 153. -/
def monsterCo1GeometryVectorPoint153Transport : Co1 :=
  monsterCo1GeometryVectorPoint110Transport * monsterCo1GeometryTransportOperator 5 *
    monsterCo1GeometryVectorPoint110Transport⁻¹ * monsterCo1GeometryVectorPoint136Transport

/-- Complete displayed binary matrix of actual transport 153. -/
def monsterCo1GeometryVectorPoint153Matrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![4129298, 11534570, 3195142, 8397565, 11584870, 8398589, 9421689, 4137859, 12576350,
      4187486, 1041033, 524874, 1956623, 451017, 8605957, 4445140, 11468640, 5709215, 9032887,
      21509, 3328262, 731288, 1948041, 8388848]

/-- First complete finite matrix product in literal actual transport 153. -/
def monsterCo1GeometryVectorPoint153AfterSignMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![24784, 41408, 8864, 8430240, 8409136, 8433728, 8400928, 8441984, 8405728, 8397392,
      8446464, 4227504, 16477371, 9438416, 14707377, 8285799, 11985157, 14768634, 15260060,
      12574978, 12749535, 13404894, 3204199, 8389632]

/-- Second complete finite matrix product in literal actual transport 153. -/
def monsterCo1GeometryVectorPoint153AfterInverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![402, 1224, 1220, 1218, 1975, 1566, 1652, 1088, 1854, 1453, 1780, 2919, 10551306, 9671305,
      16205368, 3286199, 5705740, 16056332, 13426688, 6418442, 11603968, 14090246, 8380428,
      8388608]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 24000000 in
-- Check every entry of this finite actual transport matrix in the Lean kernel.
/-- Every column of transport 153 is its actual Conway binary action. -/
theorem monsterCo1GeometryVectorPoint153Transport_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint153Transport v =
      monsterCo1GeometryVectorPoint153Matrix *ᵥ v := by
  have hx : monsterCo1GeometryVectorPoint110Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![8414096, 40960, 8396800, 8430432, 20976, 45472, 8401568, 53792, 17152, 8397040, 57888,
    4227792, 8023227, 1049692, 6383924, 8350827, 3597152, 6314239, 15325439, 4186209, 12814783,
    13469883, 11592705, 8389632] := by rfl
  have hxi : monsterCo1GeometryVectorPoint110InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![983136, 6747293, 5838077, 13281232, 972, 409, 664, 713, 1179, 1277, 8389485, 2416448,
    2025, 873, 358, 875, 10556263, 7308285, 10584314, 10949473, 1282324, 14454800, 3083, 877]
    := by rfl
  have hy : monsterCo1GeometryVectorPoint136Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![8388689, 4137102, 9421685, 983705, 4186735, 8397216, 12576307, 8397296, 12574979,
    8446016, 8439216, 3680048, 1439007, 11191776, 14154011, 14154919, 15892019, 3379403,
    13785811, 5502065, 705793, 6260699, 2276025, 8388848] := by rfl
  have he : monsterCo1GeometryVectorPoint153AfterSignMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![24784, 41408, 8864, 8430240, 8409136, 8433728, 8400928, 8441984, 8405728, 8397392,
    8446464, 4227504, 16477371, 9438416, 14707377, 8285799, 11985157, 14768634, 15260060,
    12574978, 12749535, 13404894, 3204199, 8389632] := by rfl
  have hf : monsterCo1GeometryVectorPoint153AfterInverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![402, 1224, 1220, 1218, 1975, 1566, 1652, 1088, 1854, 1453, 1780, 2919, 10551306, 9671305,
    16205368, 3286199, 5705740, 16056332, 13426688, 6418442, 11603968, 14090246, 8380428,
    8388608] := by rfl
  have hc : monsterCo1GeometryVectorPoint153Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![4129298, 11534570, 3195142, 8397565, 11584870, 8398589, 9421689, 4137859, 12576350,
    4187486, 1041033, 524874, 1956623, 451017, 8605957, 4445140, 11468640, 5709215, 9032887,
    21509, 3328262, 731288, 1948041, 8388848] := by rfl
  have hc1 : monsterCo1GeometryVectorPoint110Matrix *
    monsterCo1GeometryTransportOperatorMatrix 5 =
    monsterCo1GeometryVectorPoint153AfterSignMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![8414096, 40960, 8396800, 8430432, 20976, 45472, 8401568, 53792, 17152, 8397040, 57888,
    4227792, 8023227, 1049692, 6383924, 8350827, 3597152, 6314239, 15325439, 4186209, 12814783,
    13469883, 11592705, 8389632]
      (monsterCo1GeometryBinaryOperatorMasks 5)
    ![24784, 41408, 8864, 8430240, 8409136, 8433728, 8400928, 8441984, 8405728, 8397392,
    8446464, 4227504, 16477371, 9438416, 14707377, 8285799, 11985157, 14768634, 15260060,
    12574978, 12749535, 13404894, 3204199, 8389632] hx
    (monsterCo1GeometryBinaryOperatorMasks_decode 5) he (by decide +kernel)
  have hc2 : monsterCo1GeometryVectorPoint153AfterSignMatrix *
    monsterCo1GeometryVectorPoint110InverseMatrix =
    monsterCo1GeometryVectorPoint153AfterInverseMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![24784, 41408, 8864, 8430240, 8409136, 8433728, 8400928, 8441984, 8405728, 8397392,
    8446464, 4227504, 16477371, 9438416, 14707377, 8285799, 11985157, 14768634, 15260060,
    12574978, 12749535, 13404894, 3204199, 8389632]
    ![983136, 6747293, 5838077, 13281232, 972, 409, 664, 713, 1179, 1277, 8389485, 2416448,
    2025, 873, 358, 875, 10556263, 7308285, 10584314, 10949473, 1282324, 14454800, 3083, 877]
    ![402, 1224, 1220, 1218, 1975, 1566, 1652, 1088, 1854, 1453, 1780, 2919, 10551306, 9671305,
    16205368, 3286199, 5705740, 16056332, 13426688, 6418442, 11603968, 14090246, 8380428,
    8388608] he hxi hf (by decide +kernel)
  have hc3 : monsterCo1GeometryVectorPoint153AfterInverseMatrix *
    monsterCo1GeometryVectorPoint136Matrix = monsterCo1GeometryVectorPoint153Matrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![402, 1224, 1220, 1218, 1975, 1566, 1652, 1088, 1854, 1453, 1780, 2919, 10551306, 9671305,
    16205368, 3286199, 5705740, 16056332, 13426688, 6418442, 11603968, 14090246, 8380428,
    8388608]
    ![8388689, 4137102, 9421685, 983705, 4186735, 8397216, 12576307, 8397296, 12574979,
    8446016, 8439216, 3680048, 1439007, 11191776, 14154011, 14154919, 15892019, 3379403,
    13785811, 5502065, 705793, 6260699, 2276025, 8388848]
    ![4129298, 11534570, 3195142, 8397565, 11584870, 8398589, 9421689, 4137859, 12576350,
    4187486, 1041033, 524874, 1956623, 451017, 8605957, 4445140, 11468640, 5709215, 9032887,
    21509, 3328262, 731288, 1948041, 8388848] hf hy hc (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_line_products
    monsterCo1GeometryVectorPoint110Transport monsterCo1GeometryVectorPoint136Transport 5
    monsterCo1GeometryVectorPoint110Matrix monsterCo1GeometryVectorPoint110InverseMatrix
    monsterCo1GeometryVectorPoint136Matrix
    monsterCo1GeometryVectorPoint153AfterSignMatrix
    monsterCo1GeometryVectorPoint153AfterInverseMatrix monsterCo1GeometryVectorPoint153Matrix
    monsterCo1GeometryVectorPoint110Transport_binary
    monsterCo1GeometryVectorPoint110Transport_inverse_binary
    monsterCo1GeometryVectorPoint136Transport_binary
    hc1 hc2 hc3 v

/-- Source point 153 is the literal actual transported frame point. -/
def monsterCo1GeometryVectorPoint153 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryVectorPoint153Transport • monsterCo1GeometryBasePoint

/-- Complete binary coordinates of this literal actual source point. -/
theorem monsterCo1GeometryVectorPoint153_binary :
    monsterCo1GeometryVectorPoint153.val =
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 1, 1, 1, 0] := by
  change co1BinaryAction monsterCo1GeometryVectorPoint153Transport monsterCo1GeometryBasePoint.val =
      _
  rw [monsterCo1GeometryVectorPoint153Transport_binary, monsterCo1GeometryBasePoint_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
