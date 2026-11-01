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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint021
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint083

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The literal actual two-core word for source point 130. -/
def monsterCo1GeometryVectorPoint130Transport : Co1 :=
  monsterCo1GeometryVectorPoint21Transport * monsterCo1GeometryTransportOperator 6 *
    monsterCo1GeometryVectorPoint21Transport⁻¹ * monsterCo1GeometryVectorPoint83Transport

/-- Complete displayed binary matrix of actual transport 130. -/
def monsterCo1GeometryVectorPoint130Matrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![917780, 1309996, 611953, 8410165, 9306564, 484785, 917955, 943349, 492775, 10112476,
      458807, 3761952, 5871706, 13534591, 3845434, 16591207, 3449759, 8507358, 4531032,
      4278624, 15787367, 12617579, 774682, 34151]

/-- First complete finite matrix product in literal actual transport 130. -/
def monsterCo1GeometryVectorPoint130AfterSignMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![365049, 5016798, 684373, 9093589, 366505, 8737849, 365913, 8766649, 328148, 13020870,
      8718217, 9823312, 16017344, 10786105, 15894628, 5672877, 5070968, 3070365, 11082750,
      9072496, 10584944, 10559584, 5481552, 10224]

/-- Second complete finite matrix product in literal actual transport 130. -/
def monsterCo1GeometryVectorPoint130AfterInverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![13788408, 10557927, 10982790, 14173612, 13788393, 11358447, 15877205, 5407715, 890553,
      8808957, 889785, 2619118, 8332342, 9071153, 10940161, 15963760, 7607659, 16497627,
      11483320, 16511584, 6875700, 14159278, 9818653, 2106214]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 24000000 in
-- Check every entry of this finite actual transport matrix in the Lean kernel.
/-- Every column of transport 130 is its actual Conway binary action. -/
theorem monsterCo1GeometryVectorPoint130Transport_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint130Transport v =
      monsterCo1GeometryVectorPoint130Matrix *ᵥ v := by
  have hx : monsterCo1GeometryVectorPoint21Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![8753212, 13536263, 9073289, 9093529, 8754796, 349372, 365724, 378620, 328401, 12889667,
    8717452, 1435523, 16017024, 2397375, 15764017, 5541566, 13459633, 11328136, 11213486,
    552115, 10584547, 10559859, 5482265, 9888] := by decide +kernel
  have hxi : monsterCo1GeometryVectorPoint21InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![479330, 10505873, 9093297, 11384110, 14620496, 58432, 16724027, 57584, 8389645, 871,
    2106397, 6419317, 11593622, 10494922, 5189706, 5231722, 2004638, 728030, 3736320, 14600699,
    8423168, 12143725, 15674507, 2105580] := by decide +kernel
  have hy : monsterCo1GeometryVectorPoint83Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![8388800, 8417472, 8435536, 53648, 16, 48, 192, 58432, 24784, 41072, 58368, 6349582,
    13696015, 1074177, 10502288, 3194960, 11748283, 1197814, 14166725, 827526, 10487243,
    1107622, 9221000, 8389632] := by rfl
  have he : monsterCo1GeometryVectorPoint130AfterSignMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![365049, 5016798, 684373, 9093589, 366505, 8737849, 365913, 8766649, 328148, 13020870,
    8718217, 9823312, 16017344, 10786105, 15894628, 5672877, 5070968, 3070365, 11082750,
    9072496, 10584944, 10559584, 5481552, 10224] := by rfl
  have hf : monsterCo1GeometryVectorPoint130AfterInverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![13788408, 10557927, 10982790, 14173612, 13788393, 11358447, 15877205, 5407715, 890553,
    8808957, 889785, 2619118, 8332342, 9071153, 10940161, 15963760, 7607659, 16497627,
    11483320, 16511584, 6875700, 14159278, 9818653, 2106214] := by rfl
  have hc : monsterCo1GeometryVectorPoint130Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![917780, 1309996, 611953, 8410165, 9306564, 484785, 917955, 943349, 492775, 10112476,
    458807, 3761952, 5871706, 13534591, 3845434, 16591207, 3449759, 8507358, 4531032, 4278624,
    15787367, 12617579, 774682, 34151] := by rfl
  have hc1 : monsterCo1GeometryVectorPoint21Matrix *
    monsterCo1GeometryTransportOperatorMatrix 6 =
    monsterCo1GeometryVectorPoint130AfterSignMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![8753212, 13536263, 9073289, 9093529, 8754796, 349372, 365724, 378620, 328401, 12889667,
    8717452, 1435523, 16017024, 2397375, 15764017, 5541566, 13459633, 11328136, 11213486,
    552115, 10584547, 10559859, 5482265, 9888]
      (monsterCo1GeometryBinaryOperatorMasks 6)
    ![365049, 5016798, 684373, 9093589, 366505, 8737849, 365913, 8766649, 328148, 13020870,
    8718217, 9823312, 16017344, 10786105, 15894628, 5672877, 5070968, 3070365, 11082750,
    9072496, 10584944, 10559584, 5481552, 10224] hx
    (monsterCo1GeometryBinaryOperatorMasks_decode 6) he (by decide +kernel)
  have hc2 : monsterCo1GeometryVectorPoint130AfterSignMatrix *
    monsterCo1GeometryVectorPoint21InverseMatrix =
    monsterCo1GeometryVectorPoint130AfterInverseMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![365049, 5016798, 684373, 9093589, 366505, 8737849, 365913, 8766649, 328148, 13020870,
    8718217, 9823312, 16017344, 10786105, 15894628, 5672877, 5070968, 3070365, 11082750,
    9072496, 10584944, 10559584, 5481552, 10224]
    ![479330, 10505873, 9093297, 11384110, 14620496, 58432, 16724027, 57584, 8389645, 871,
    2106397, 6419317, 11593622, 10494922, 5189706, 5231722, 2004638, 728030, 3736320, 14600699,
    8423168, 12143725, 15674507, 2105580]
    ![13788408, 10557927, 10982790, 14173612, 13788393, 11358447, 15877205, 5407715, 890553,
    8808957, 889785, 2619118, 8332342, 9071153, 10940161, 15963760, 7607659, 16497627,
    11483320, 16511584, 6875700, 14159278, 9818653, 2106214] he hxi hf (by decide +kernel)
  have hc3 : monsterCo1GeometryVectorPoint130AfterInverseMatrix *
    monsterCo1GeometryVectorPoint83Matrix = monsterCo1GeometryVectorPoint130Matrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![13788408, 10557927, 10982790, 14173612, 13788393, 11358447, 15877205, 5407715, 890553,
    8808957, 889785, 2619118, 8332342, 9071153, 10940161, 15963760, 7607659, 16497627,
    11483320, 16511584, 6875700, 14159278, 9818653, 2106214]
    ![8388800, 8417472, 8435536, 53648, 16, 48, 192, 58432, 24784, 41072, 58368, 6349582,
    13696015, 1074177, 10502288, 3194960, 11748283, 1197814, 14166725, 827526, 10487243,
    1107622, 9221000, 8389632]
    ![917780, 1309996, 611953, 8410165, 9306564, 484785, 917955, 943349, 492775, 10112476,
    458807, 3761952, 5871706, 13534591, 3845434, 16591207, 3449759, 8507358, 4531032, 4278624,
    15787367, 12617579, 774682, 34151] hf hy hc (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_line_products
    monsterCo1GeometryVectorPoint21Transport monsterCo1GeometryVectorPoint83Transport 6
    monsterCo1GeometryVectorPoint21Matrix monsterCo1GeometryVectorPoint21InverseMatrix
    monsterCo1GeometryVectorPoint83Matrix
    monsterCo1GeometryVectorPoint130AfterSignMatrix
    monsterCo1GeometryVectorPoint130AfterInverseMatrix monsterCo1GeometryVectorPoint130Matrix
    monsterCo1GeometryVectorPoint21Transport_binary
    monsterCo1GeometryVectorPoint21Transport_inverse_binary
    monsterCo1GeometryVectorPoint83Transport_binary
    hc1 hc2 hc3 v

/-- Source point 130 is the literal actual transported frame point. -/
def monsterCo1GeometryVectorPoint130 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryVectorPoint130Transport • monsterCo1GeometryBasePoint

/-- Complete binary coordinates of this literal actual source point. -/
theorem monsterCo1GeometryVectorPoint130_binary :
    monsterCo1GeometryVectorPoint130.val =
      ![0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 0, 0, 0] := by
  change co1BinaryAction monsterCo1GeometryVectorPoint130Transport monsterCo1GeometryBasePoint.val =
      _
  rw [monsterCo1GeometryVectorPoint130Transport_binary, monsterCo1GeometryBasePoint_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
