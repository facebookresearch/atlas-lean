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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint035
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint037

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The literal actual two-core word for source point 82. -/
def monsterCo1GeometryVectorPoint82Transport : Co1 :=
  monsterCo1GeometryVectorPoint35Transport * monsterCo1GeometryTransportOperator 5 *
    monsterCo1GeometryVectorPoint35Transport⁻¹ * monsterCo1GeometryVectorPoint37Transport

/-- Complete displayed binary matrix of actual transport 82. -/
def monsterCo1GeometryVectorPoint82Matrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![58529, 11003705, 10969406, 491731, 1152, 57504, 8446144, 8446016, 26608, 1504, 8389632,
      8496796, 8860884, 2138972, 10495547, 26086, 12925741, 1340223, 6830355, 8175491, 18043,
      11551158, 3287332, 8388784]

/-- First complete finite matrix product in literal actual transport 82. -/
def monsterCo1GeometryVectorPoint82AfterSignMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![8388609, 12655648, 15857735, 14809291, 8388624, 8388656, 192, 64, 8414096, 8430000,
      8389632, 5315234, 13700748, 9496237, 10487242, 11536198, 237957, 156553, 8954556,
      9200284, 8388730, 8388822, 130560, 57376]

/-- Second complete finite matrix product in literal actual transport 82. -/
def monsterCo1GeometryVectorPoint82AfterInverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![1, 3395569, 9644822, 10693418, 8446993, 8447009, 64, 128, 25990, 42570, 1024, 247747,
      8600562, 11584513, 1065184, 2130128, 92233, 174213, 10757149, 9970733, 9495553, 10544129,
      15936450, 58417]

set_option maxHeartbeats 24000000 in
-- Check every entry of this finite actual transport matrix in the Lean kernel.
/-- Every column of transport 82 is its actual Conway binary action. -/
theorem monsterCo1GeometryVectorPoint82Transport_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint82Transport v =
      monsterCo1GeometryVectorPoint82Matrix *ᵥ v := by
  have hx : monsterCo1GeometryVectorPoint35Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![8388609, 4201487, 15792142, 14743566, 16, 48, 192, 64, 24784, 41072, 8389632, 13638145,
    13635087, 1107457, 10487040, 11536128, 237642, 155846, 565370, 811222, 122, 214, 65039,
    8445952] := by decide +kernel
  have hxi : monsterCo1GeometryVectorPoint35InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![8446976, 3198194, 1100962, 2149458, 16, 48, 128, 192, 8405003, 49164, 8445953, 12638221,
    8401923, 59377, 59041, 58705, 3343296, 2228544, 3933168, 1311392, 12, 8389643, 4203535,
    8446977] := by decide +kernel
  have hy : monsterCo1GeometryVectorPoint37Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![58529, 12635279, 15788942, 14739854, 8389648, 8446000, 8446144, 8446016, 8421584,
    8405104, 8389632, 5664455, 13637695, 1090561, 10518624, 11542608, 4430948, 9598662,
    5824133, 16563192, 8406763, 3162406, 14018082, 58368] := by decide +kernel
  have he : monsterCo1GeometryVectorPoint82AfterSignMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![8388609, 12655648, 15857735, 14809291, 8388624, 8388656, 192, 64, 8414096, 8430000,
    8389632, 5315234, 13700748, 9496237, 10487242, 11536198, 237957, 156553, 8954556, 9200284,
    8388730, 8388822, 130560, 57376] := by rfl
  have hf : monsterCo1GeometryVectorPoint82AfterInverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![1, 3395569, 9644822, 10693418, 8446993, 8447009, 64, 128, 25990, 42570, 1024, 247747,
    8600562, 11584513, 1065184, 2130128, 92233, 174213, 10757149, 9970733, 9495553, 10544129,
    15936450, 58417] := by rfl
  have hc : monsterCo1GeometryVectorPoint82Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![58529, 11003705, 10969406, 491731, 1152, 57504, 8446144, 8446016, 26608, 1504, 8389632,
    8496796, 8860884, 2138972, 10495547, 26086, 12925741, 1340223, 6830355, 8175491, 18043,
    11551158, 3287332, 8388784] := by rfl
  have hc1 : monsterCo1GeometryVectorPoint35Matrix *
    monsterCo1GeometryTransportOperatorMatrix 5 =
    monsterCo1GeometryVectorPoint82AfterSignMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![8388609, 4201487, 15792142, 14743566, 16, 48, 192, 64, 24784, 41072, 8389632, 13638145,
    13635087, 1107457, 10487040, 11536128, 237642, 155846, 565370, 811222, 122, 214, 65039,
    8445952]
      (monsterCo1GeometryBinaryOperatorMasks 5)
    ![8388609, 12655648, 15857735, 14809291, 8388624, 8388656, 192, 64, 8414096, 8430000,
    8389632, 5315234, 13700748, 9496237, 10487242, 11536198, 237957, 156553, 8954556, 9200284,
    8388730, 8388822, 130560, 57376] hx (monsterCo1GeometryBinaryOperatorMasks_decode 5) he (by
    decide +kernel)
  have hc2 : monsterCo1GeometryVectorPoint82AfterSignMatrix *
    monsterCo1GeometryVectorPoint35InverseMatrix =
    monsterCo1GeometryVectorPoint82AfterInverseMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![8388609, 12655648, 15857735, 14809291, 8388624, 8388656, 192, 64, 8414096, 8430000,
    8389632, 5315234, 13700748, 9496237, 10487242, 11536198, 237957, 156553, 8954556, 9200284,
    8388730, 8388822, 130560, 57376]
    ![8446976, 3198194, 1100962, 2149458, 16, 48, 128, 192, 8405003, 49164, 8445953, 12638221,
    8401923, 59377, 59041, 58705, 3343296, 2228544, 3933168, 1311392, 12, 8389643, 4203535,
    8446977]
    ![1, 3395569, 9644822, 10693418, 8446993, 8447009, 64, 128, 25990, 42570, 1024, 247747,
    8600562, 11584513, 1065184, 2130128, 92233, 174213, 10757149, 9970733, 9495553, 10544129,
    15936450, 58417] he hxi hf (by decide +kernel)
  have hc3 : monsterCo1GeometryVectorPoint82AfterInverseMatrix *
    monsterCo1GeometryVectorPoint37Matrix = monsterCo1GeometryVectorPoint82Matrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![1, 3395569, 9644822, 10693418, 8446993, 8447009, 64, 128, 25990, 42570, 1024, 247747,
    8600562, 11584513, 1065184, 2130128, 92233, 174213, 10757149, 9970733, 9495553, 10544129,
    15936450, 58417]
    ![58529, 12635279, 15788942, 14739854, 8389648, 8446000, 8446144, 8446016, 8421584,
    8405104, 8389632, 5664455, 13637695, 1090561, 10518624, 11542608, 4430948, 9598662,
    5824133, 16563192, 8406763, 3162406, 14018082, 58368]
    ![58529, 11003705, 10969406, 491731, 1152, 57504, 8446144, 8446016, 26608, 1504, 8389632,
    8496796, 8860884, 2138972, 10495547, 26086, 12925741, 1340223, 6830355, 8175491, 18043,
    11551158, 3287332, 8388784] hf hy hc (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_line_products
    monsterCo1GeometryVectorPoint35Transport monsterCo1GeometryVectorPoint37Transport 5
    monsterCo1GeometryVectorPoint35Matrix monsterCo1GeometryVectorPoint35InverseMatrix
    monsterCo1GeometryVectorPoint37Matrix
    monsterCo1GeometryVectorPoint82AfterSignMatrix
    monsterCo1GeometryVectorPoint82AfterInverseMatrix monsterCo1GeometryVectorPoint82Matrix
    monsterCo1GeometryVectorPoint35Transport_binary
    monsterCo1GeometryVectorPoint35Transport_inverse_binary
    monsterCo1GeometryVectorPoint37Transport_binary
    hc1 hc2 hc3 v

/-- Source point 82 is the literal actual transported frame point. -/
def monsterCo1GeometryVectorPoint82 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryVectorPoint82Transport • monsterCo1GeometryBasePoint

/-- Complete binary coordinates of this literal actual source point. -/
theorem monsterCo1GeometryVectorPoint82_binary :
    monsterCo1GeometryVectorPoint82.val =
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0] := by
  change co1BinaryAction monsterCo1GeometryVectorPoint82Transport monsterCo1GeometryBasePoint.val =
      _
  rw [monsterCo1GeometryVectorPoint82Transport_binary, monsterCo1GeometryBasePoint_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
