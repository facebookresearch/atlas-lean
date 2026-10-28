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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint029
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint153

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The literal actual two-core word for source point 155. -/
def monsterCo1GeometryVectorPoint155Transport : Co1 :=
  monsterCo1GeometryVectorPoint29Transport * monsterCo1GeometryTransportOperator 5 *
    monsterCo1GeometryVectorPoint29Transport⁻¹ * monsterCo1GeometryVectorPoint153Transport

/-- Complete displayed binary matrix of actual transport 155. -/
def monsterCo1GeometryVectorPoint155Matrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![3196566, 4186866, 3195142, 8390493, 12517858, 8398589, 9421689, 11591930, 4178114,
      4179007, 1041033, 12184016, 5368402, 4903060, 13590616, 4445140, 11468356, 15136261,
      11692949, 29760, 8312862, 314457, 2904367, 8388848]

/-- First complete finite matrix product in literal actual transport 155. -/
def monsterCo1GeometryVectorPoint155AfterSignMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![57584, 53856, 8450752, 45904, 57488, 1152, 8388640, 8446016, 8438192, 50112, 8388768,
      10922685, 349076, 9461942, 1074971, 876, 11818005, 6707933, 7920180, 2205460, 3196013,
      2115041, 14633659, 8389632]

/-- Second complete finite matrix product in literal actual transport 155. -/
def monsterCo1GeometryVectorPoint155AfterInverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![8389665, 8390642, 4, 271, 8389680, 32, 64, 192, 720, 8390064, 1024, 2177472, 37888,
      41984, 50176, 32768, 3221440, 2306496, 10232752, 12066928, 10527856, 1057872, 6370071,
      8388608]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 24000000 in
-- Check every entry of this finite actual transport matrix in the Lean kernel.
/-- Every column of transport 155 is its actual Conway binary action. -/
theorem monsterCo1GeometryVectorPoint155Transport_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint155Transport v =
      monsterCo1GeometryVectorPoint155Matrix *ᵥ v := by
  have hx : monsterCo1GeometryVectorPoint29Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![57552, 8442048, 8450752, 45744, 57520, 1152, 8388640, 57440, 49968, 49472, 8388768,
    2599355, 8736856, 1074042, 9462999, 876, 3430303, 15161819, 7986139, 10593822, 3196587,
    10503371, 14568157, 8389632] := by decide +kernel
  have hxi : monsterCo1GeometryVectorPoint29InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![57457, 9031814, 3766135, 12186048, 8388833, 8389664, 8389681, 1088, 1366, 8389616, 1120,
    4484773, 8390516, 8389622, 1180, 8390651, 9540855, 14516490, 2651759, 12842868, 11534458,
    1099226, 134036, 8389728] := by decide +kernel
  have hy : monsterCo1GeometryVectorPoint153Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![4129298, 11534570, 3195142, 8397565, 11584870, 8398589, 9421689, 4137859, 12576350,
    4187486, 1041033, 524874, 1956623, 451017, 8605957, 4445140, 11468640, 5709215, 9032887,
    21509, 3328262, 731288, 1948041, 8388848] := by rfl
  have he : monsterCo1GeometryVectorPoint155AfterSignMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![57584, 53856, 8450752, 45904, 57488, 1152, 8388640, 8446016, 8438192, 50112, 8388768,
    10922685, 349076, 9461942, 1074971, 876, 11818005, 6707933, 7920180, 2205460, 3196013,
    2115041, 14633659, 8389632] := by rfl
  have hf : monsterCo1GeometryVectorPoint155AfterInverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![8389665, 8390642, 4, 271, 8389680, 32, 64, 192, 720, 8390064, 1024, 2177472, 37888,
    41984, 50176, 32768, 3221440, 2306496, 10232752, 12066928, 10527856, 1057872, 6370071,
    8388608] := by rfl
  have hc : monsterCo1GeometryVectorPoint155Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![3196566, 4186866, 3195142, 8390493, 12517858, 8398589, 9421689, 11591930, 4178114,
    4179007, 1041033, 12184016, 5368402, 4903060, 13590616, 4445140, 11468356, 15136261,
    11692949, 29760, 8312862, 314457, 2904367, 8388848] := by rfl
  have hc1 : monsterCo1GeometryVectorPoint29Matrix *
    monsterCo1GeometryTransportOperatorMatrix 5 =
    monsterCo1GeometryVectorPoint155AfterSignMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![57552, 8442048, 8450752, 45744, 57520, 1152, 8388640, 57440, 49968, 49472, 8388768,
    2599355, 8736856, 1074042, 9462999, 876, 3430303, 15161819, 7986139, 10593822, 3196587,
    10503371, 14568157, 8389632]
      (monsterCo1GeometryBinaryOperatorMasks 5)
    ![57584, 53856, 8450752, 45904, 57488, 1152, 8388640, 8446016, 8438192, 50112, 8388768,
    10922685, 349076, 9461942, 1074971, 876, 11818005, 6707933, 7920180, 2205460, 3196013,
    2115041, 14633659, 8389632] hx (monsterCo1GeometryBinaryOperatorMasks_decode 5) he (by
    decide +kernel)
  have hc2 : monsterCo1GeometryVectorPoint155AfterSignMatrix *
    monsterCo1GeometryVectorPoint29InverseMatrix =
    monsterCo1GeometryVectorPoint155AfterInverseMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![57584, 53856, 8450752, 45904, 57488, 1152, 8388640, 8446016, 8438192, 50112, 8388768,
    10922685, 349076, 9461942, 1074971, 876, 11818005, 6707933, 7920180, 2205460, 3196013,
    2115041, 14633659, 8389632]
    ![57457, 9031814, 3766135, 12186048, 8388833, 8389664, 8389681, 1088, 1366, 8389616, 1120,
    4484773, 8390516, 8389622, 1180, 8390651, 9540855, 14516490, 2651759, 12842868, 11534458,
    1099226, 134036, 8389728]
    ![8389665, 8390642, 4, 271, 8389680, 32, 64, 192, 720, 8390064, 1024, 2177472, 37888,
    41984, 50176, 32768, 3221440, 2306496, 10232752, 12066928, 10527856, 1057872, 6370071,
    8388608] he hxi hf (by decide +kernel)
  have hc3 : monsterCo1GeometryVectorPoint155AfterInverseMatrix *
    monsterCo1GeometryVectorPoint153Matrix = monsterCo1GeometryVectorPoint155Matrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![8389665, 8390642, 4, 271, 8389680, 32, 64, 192, 720, 8390064, 1024, 2177472, 37888,
    41984, 50176, 32768, 3221440, 2306496, 10232752, 12066928, 10527856, 1057872, 6370071,
    8388608]
    ![4129298, 11534570, 3195142, 8397565, 11584870, 8398589, 9421689, 4137859, 12576350,
    4187486, 1041033, 524874, 1956623, 451017, 8605957, 4445140, 11468640, 5709215, 9032887,
    21509, 3328262, 731288, 1948041, 8388848]
    ![3196566, 4186866, 3195142, 8390493, 12517858, 8398589, 9421689, 11591930, 4178114,
    4179007, 1041033, 12184016, 5368402, 4903060, 13590616, 4445140, 11468356, 15136261,
    11692949, 29760, 8312862, 314457, 2904367, 8388848] hf hy hc (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_line_products
    monsterCo1GeometryVectorPoint29Transport monsterCo1GeometryVectorPoint153Transport 5
    monsterCo1GeometryVectorPoint29Matrix monsterCo1GeometryVectorPoint29InverseMatrix
    monsterCo1GeometryVectorPoint153Matrix
    monsterCo1GeometryVectorPoint155AfterSignMatrix
    monsterCo1GeometryVectorPoint155AfterInverseMatrix monsterCo1GeometryVectorPoint155Matrix
    monsterCo1GeometryVectorPoint29Transport_binary
    monsterCo1GeometryVectorPoint29Transport_inverse_binary
    monsterCo1GeometryVectorPoint153Transport_binary
    hc1 hc2 hc3 v

/-- Source point 155 is the literal actual transported frame point. -/
def monsterCo1GeometryVectorPoint155 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryVectorPoint155Transport • monsterCo1GeometryBasePoint

/-- Complete binary coordinates of this literal actual source point. -/
theorem monsterCo1GeometryVectorPoint155_binary :
    monsterCo1GeometryVectorPoint155.val =
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 1, 0, 0] := by
  change co1BinaryAction monsterCo1GeometryVectorPoint155Transport monsterCo1GeometryBasePoint.val =
      _
  rw [monsterCo1GeometryVectorPoint155Transport_binary, monsterCo1GeometryBasePoint_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
