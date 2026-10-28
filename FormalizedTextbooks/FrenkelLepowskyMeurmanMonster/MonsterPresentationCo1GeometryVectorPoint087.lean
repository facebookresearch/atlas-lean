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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint039

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The literal actual two-core word for source point 87. -/
def monsterCo1GeometryVectorPoint87Transport : Co1 :=
  monsterCo1GeometryVectorPoint29Transport * monsterCo1GeometryTransportOperator 1 *
    monsterCo1GeometryVectorPoint29Transport⁻¹ * monsterCo1GeometryVectorPoint39Transport

/-- Complete displayed binary matrix of actual transport 87. -/
def monsterCo1GeometryVectorPoint87Matrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![161, 12635279, 15732622, 14739854, 8389648, 8389680, 8446144, 8389696, 8421584, 8405104,
      8389632, 2634376, 13637679, 1090561, 2155520, 11550944, 2307515, 8532214, 11023707,
      7117240, 9495771, 3196310, 2428173, 58368]

/-- First complete finite matrix product in literal actual transport 87. -/
def monsterCo1GeometryVectorPoint87AfterSignMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![8447184, 8442048, 63168, 45744, 8447152, 1152, 8388640, 8447072, 49968, 49472, 8388768,
      10991749, 349304, 1073530, 1074903, 876, 3428511, 15158507, 16369915, 10594110, 11584939,
      10502603, 14572749, 8389632]

/-- Second complete finite matrix product in literal actual transport 87. -/
def monsterCo1GeometryVectorPoint87AfterInverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![8388609, 2, 8388612, 8, 8388624, 32, 64, 8388736, 256, 512, 1024, 613554, 5152, 8397808,
      18320, 32768, 8454854, 8520323, 262546, 8913270, 1049286, 2097462, 12582917, 8388608]

set_option maxHeartbeats 24000000 in
-- Check every entry of this finite actual transport matrix in the Lean kernel.
/-- Every column of transport 87 is its actual Conway binary action. -/
theorem monsterCo1GeometryVectorPoint87Transport_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint87Transport v =
      monsterCo1GeometryVectorPoint87Matrix *ᵥ v := by
  have hx : monsterCo1GeometryVectorPoint29Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![57552, 8442048, 8450752, 45744, 57520, 1152, 8388640, 57440, 49968, 49472, 8388768,
    2599355, 8736856, 1074042, 9462999, 876, 3430303, 15161819, 7986139, 10593822, 3196587,
    10503371, 14568157, 8389632] := by decide +kernel
  have hxi : monsterCo1GeometryVectorPoint29InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![57457, 9031814, 3766135, 12186048, 8388833, 8389664, 8389681, 1088, 1366, 8389616, 1120,
    4484773, 8390516, 8389622, 1180, 8390651, 9540855, 14516490, 2651759, 12842868, 11534458,
    1099226, 134036, 8389728] := by decide +kernel
  have hy : monsterCo1GeometryVectorPoint39Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![58529, 12635279, 15788942, 14739854, 8445968, 8389680, 8446144, 8446016, 8421584,
    8405104, 8389632, 5746251, 13637663, 1074177, 10494192, 11550944, 9680458, 4349160,
    15235412, 6086281, 2130730, 8423015, 14018082, 58368] := by decide +kernel
  have he : monsterCo1GeometryVectorPoint87AfterSignMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![8447184, 8442048, 63168, 45744, 8447152, 1152, 8388640, 8447072, 49968, 49472, 8388768,
    10991749, 349304, 1073530, 1074903, 876, 3428511, 15158507, 16369915, 10594110, 11584939,
    10502603, 14572749, 8389632] := by rfl
  have hf : monsterCo1GeometryVectorPoint87AfterInverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![8388609, 2, 8388612, 8, 8388624, 32, 64, 8388736, 256, 512, 1024, 613554, 5152, 8397808,
    18320, 32768, 8454854, 8520323, 262546, 8913270, 1049286, 2097462, 12582917, 8388608] := by rfl
  have hc : monsterCo1GeometryVectorPoint87Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![161, 12635279, 15732622, 14739854, 8389648, 8389680, 8446144, 8389696, 8421584, 8405104,
    8389632, 2634376, 13637679, 1090561, 2155520, 11550944, 2307515, 8532214, 11023707,
    7117240, 9495771, 3196310, 2428173, 58368] := by rfl
  have hc1 : monsterCo1GeometryVectorPoint29Matrix *
    monsterCo1GeometryTransportOperatorMatrix 1 =
    monsterCo1GeometryVectorPoint87AfterSignMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![57552, 8442048, 8450752, 45744, 57520, 1152, 8388640, 57440, 49968, 49472, 8388768,
    2599355, 8736856, 1074042, 9462999, 876, 3430303, 15161819, 7986139, 10593822, 3196587,
    10503371, 14568157, 8389632]
      (monsterCo1GeometryBinaryOperatorMasks 1)
    ![8447184, 8442048, 63168, 45744, 8447152, 1152, 8388640, 8447072, 49968, 49472, 8388768,
    10991749, 349304, 1073530, 1074903, 876, 3428511, 15158507, 16369915, 10594110, 11584939,
    10502603, 14572749, 8389632] hx (monsterCo1GeometryBinaryOperatorMasks_decode 1) he (by
    decide +kernel)
  have hc2 : monsterCo1GeometryVectorPoint87AfterSignMatrix *
    monsterCo1GeometryVectorPoint29InverseMatrix =
    monsterCo1GeometryVectorPoint87AfterInverseMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![8447184, 8442048, 63168, 45744, 8447152, 1152, 8388640, 8447072, 49968, 49472, 8388768,
    10991749, 349304, 1073530, 1074903, 876, 3428511, 15158507, 16369915, 10594110, 11584939,
    10502603, 14572749, 8389632]
    ![57457, 9031814, 3766135, 12186048, 8388833, 8389664, 8389681, 1088, 1366, 8389616, 1120,
    4484773, 8390516, 8389622, 1180, 8390651, 9540855, 14516490, 2651759, 12842868, 11534458,
    1099226, 134036, 8389728]
    ![8388609, 2, 8388612, 8, 8388624, 32, 64, 8388736, 256, 512, 1024, 613554, 5152, 8397808,
    18320, 32768, 8454854, 8520323, 262546, 8913270, 1049286, 2097462, 12582917, 8388608] he
    hxi hf (by decide +kernel)
  have hc3 : monsterCo1GeometryVectorPoint87AfterInverseMatrix *
    monsterCo1GeometryVectorPoint39Matrix = monsterCo1GeometryVectorPoint87Matrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![8388609, 2, 8388612, 8, 8388624, 32, 64, 8388736, 256, 512, 1024, 613554, 5152, 8397808,
    18320, 32768, 8454854, 8520323, 262546, 8913270, 1049286, 2097462, 12582917, 8388608]
    ![58529, 12635279, 15788942, 14739854, 8445968, 8389680, 8446144, 8446016, 8421584,
    8405104, 8389632, 5746251, 13637663, 1074177, 10494192, 11550944, 9680458, 4349160,
    15235412, 6086281, 2130730, 8423015, 14018082, 58368]
    ![161, 12635279, 15732622, 14739854, 8389648, 8389680, 8446144, 8389696, 8421584, 8405104,
    8389632, 2634376, 13637679, 1090561, 2155520, 11550944, 2307515, 8532214, 11023707,
    7117240, 9495771, 3196310, 2428173, 58368] hf hy hc (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_line_products
    monsterCo1GeometryVectorPoint29Transport monsterCo1GeometryVectorPoint39Transport 1
    monsterCo1GeometryVectorPoint29Matrix monsterCo1GeometryVectorPoint29InverseMatrix
    monsterCo1GeometryVectorPoint39Matrix
    monsterCo1GeometryVectorPoint87AfterSignMatrix
    monsterCo1GeometryVectorPoint87AfterInverseMatrix monsterCo1GeometryVectorPoint87Matrix
    monsterCo1GeometryVectorPoint29Transport_binary
    monsterCo1GeometryVectorPoint29Transport_inverse_binary
    monsterCo1GeometryVectorPoint39Transport_binary
    hc1 hc2 hc3 v

/-- Source point 87 is the literal actual transported frame point. -/
def monsterCo1GeometryVectorPoint87 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryVectorPoint87Transport • monsterCo1GeometryBasePoint

/-- Complete binary coordinates of this literal actual source point. -/
theorem monsterCo1GeometryVectorPoint87_binary :
    monsterCo1GeometryVectorPoint87.val =
      ![0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0] := by
  change co1BinaryAction monsterCo1GeometryVectorPoint87Transport monsterCo1GeometryBasePoint.val =
      _
  rw [monsterCo1GeometryVectorPoint87Transport_binary, monsterCo1GeometryBasePoint_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
