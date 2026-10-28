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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint005
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint035

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The literal actual two-core word for source point 72. -/
def monsterCo1GeometryVectorPoint72Transport : Co1 :=
  monsterCo1GeometryVectorPoint5Transport * monsterCo1GeometryTransportOperator 1 *
    monsterCo1GeometryVectorPoint5Transport⁻¹ * monsterCo1GeometryVectorPoint35Transport

/-- Complete displayed binary matrix of actual transport 72. -/
def monsterCo1GeometryVectorPoint72Matrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![57345, 4201487, 7346190, 14743566, 8445968, 48, 192, 8446016, 24784, 41072, 8389632,
      7326205, 5245503, 9487873, 2146800, 11536128, 3343547, 4340984, 4775157, 3933415,
      11551883, 11568167, 15787520, 8445952]

/-- First complete finite matrix product in literal actual transport 72. -/
def monsterCo1GeometryVectorPoint72AfterSignMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![8447184, 8442048, 63168, 45744, 8447152, 8388736, 8388640, 8447072, 49968, 49472,
      8388768, 4228110, 373960, 9454298, 9461879, 50908, 3416319, 15158507, 7973115, 10559614,
      3147755, 2098587, 14572749, 8389632]

/-- Second complete finite matrix product in literal actual transport 72. -/
def monsterCo1GeometryVectorPoint72AfterInverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![8388609, 2, 8388612, 8, 8388624, 32, 64, 8388736, 256, 512, 1024, 613554, 5152, 8397808,
      18320, 32768, 8454854, 8520323, 262546, 8913270, 1049286, 2097462, 12582917, 8388608]

set_option maxHeartbeats 24000000 in
-- Check every entry of this finite actual transport matrix in the Lean kernel.
/-- Every column of transport 72 is its actual Conway binary action. -/
theorem monsterCo1GeometryVectorPoint72Transport_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint72Transport v =
      monsterCo1GeometryVectorPoint72Matrix *ᵥ v := by
  have hx : monsterCo1GeometryVectorPoint5Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![57552, 8442048, 8450752, 45744, 57520, 8388736, 8388640, 57440, 49968, 49472, 8388768,
    12615680, 373992, 1066202, 1073783, 50908, 3418111, 15161819, 16366555, 2172254, 11535595,
    10486939, 14568157, 8389632] := by decide +kernel
  have hxi : monsterCo1GeometryVectorPoint5InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![57441, 643285, 3765294, 12185673, 225, 1056, 1073, 1088, 1366, 1008, 8389728, 13004640,
    1908, 1014, 1180, 2043, 1152766, 6127893, 2651647, 4454267, 3145968, 1098844, 2971, 1120]
    := by decide +kernel
  have hy : monsterCo1GeometryVectorPoint35Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![8388609, 4201487, 15792142, 14743566, 16, 48, 192, 64, 24784, 41072, 8389632, 13638145,
    13635087, 1107457, 10487040, 11536128, 237642, 155846, 565370, 811222, 122, 214, 65039,
    8445952] := by decide +kernel
  have he : monsterCo1GeometryVectorPoint72AfterSignMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![8447184, 8442048, 63168, 45744, 8447152, 8388736, 8388640, 8447072, 49968, 49472,
    8388768, 4228110, 373960, 9454298, 9461879, 50908, 3416319, 15158507, 7973115, 10559614,
    3147755, 2098587, 14572749, 8389632] := by rfl
  have hf : monsterCo1GeometryVectorPoint72AfterInverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![8388609, 2, 8388612, 8, 8388624, 32, 64, 8388736, 256, 512, 1024, 613554, 5152, 8397808,
    18320, 32768, 8454854, 8520323, 262546, 8913270, 1049286, 2097462, 12582917, 8388608] := by rfl
  have hc : monsterCo1GeometryVectorPoint72Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![57345, 4201487, 7346190, 14743566, 8445968, 48, 192, 8446016, 24784, 41072, 8389632,
    7326205, 5245503, 9487873, 2146800, 11536128, 3343547, 4340984, 4775157, 3933415, 11551883,
    11568167, 15787520, 8445952] := by rfl
  have hc1 : monsterCo1GeometryVectorPoint5Matrix * monsterCo1GeometryTransportOperatorMatrix
    1 = monsterCo1GeometryVectorPoint72AfterSignMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![57552, 8442048, 8450752, 45744, 57520, 8388736, 8388640, 57440, 49968, 49472, 8388768,
    12615680, 373992, 1066202, 1073783, 50908, 3418111, 15161819, 16366555, 2172254, 11535595,
    10486939, 14568157, 8389632]
      (monsterCo1GeometryBinaryOperatorMasks 1)
    ![8447184, 8442048, 63168, 45744, 8447152, 8388736, 8388640, 8447072, 49968, 49472,
    8388768, 4228110, 373960, 9454298, 9461879, 50908, 3416319, 15158507, 7973115, 10559614,
    3147755, 2098587, 14572749, 8389632] hx (monsterCo1GeometryBinaryOperatorMasks_decode 1) he
    (by decide +kernel)
  have hc2 : monsterCo1GeometryVectorPoint72AfterSignMatrix *
    monsterCo1GeometryVectorPoint5InverseMatrix =
    monsterCo1GeometryVectorPoint72AfterInverseMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![8447184, 8442048, 63168, 45744, 8447152, 8388736, 8388640, 8447072, 49968, 49472,
    8388768, 4228110, 373960, 9454298, 9461879, 50908, 3416319, 15158507, 7973115, 10559614,
    3147755, 2098587, 14572749, 8389632]
    ![57441, 643285, 3765294, 12185673, 225, 1056, 1073, 1088, 1366, 1008, 8389728, 13004640,
    1908, 1014, 1180, 2043, 1152766, 6127893, 2651647, 4454267, 3145968, 1098844, 2971, 1120]
    ![8388609, 2, 8388612, 8, 8388624, 32, 64, 8388736, 256, 512, 1024, 613554, 5152, 8397808,
    18320, 32768, 8454854, 8520323, 262546, 8913270, 1049286, 2097462, 12582917, 8388608] he
    hxi hf (by decide +kernel)
  have hc3 : monsterCo1GeometryVectorPoint72AfterInverseMatrix *
    monsterCo1GeometryVectorPoint35Matrix = monsterCo1GeometryVectorPoint72Matrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![8388609, 2, 8388612, 8, 8388624, 32, 64, 8388736, 256, 512, 1024, 613554, 5152, 8397808,
    18320, 32768, 8454854, 8520323, 262546, 8913270, 1049286, 2097462, 12582917, 8388608]
    ![8388609, 4201487, 15792142, 14743566, 16, 48, 192, 64, 24784, 41072, 8389632, 13638145,
    13635087, 1107457, 10487040, 11536128, 237642, 155846, 565370, 811222, 122, 214, 65039,
    8445952]
    ![57345, 4201487, 7346190, 14743566, 8445968, 48, 192, 8446016, 24784, 41072, 8389632,
    7326205, 5245503, 9487873, 2146800, 11536128, 3343547, 4340984, 4775157, 3933415, 11551883,
    11568167, 15787520, 8445952] hf hy hc (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_line_products
    monsterCo1GeometryVectorPoint5Transport monsterCo1GeometryVectorPoint35Transport 1
    monsterCo1GeometryVectorPoint5Matrix monsterCo1GeometryVectorPoint5InverseMatrix
    monsterCo1GeometryVectorPoint35Matrix
    monsterCo1GeometryVectorPoint72AfterSignMatrix
    monsterCo1GeometryVectorPoint72AfterInverseMatrix monsterCo1GeometryVectorPoint72Matrix
    monsterCo1GeometryVectorPoint5Transport_binary
    monsterCo1GeometryVectorPoint5Transport_inverse_binary
    monsterCo1GeometryVectorPoint35Transport_binary
    hc1 hc2 hc3 v

/-- Source point 72 is the literal actual transported frame point. -/
def monsterCo1GeometryVectorPoint72 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryVectorPoint72Transport • monsterCo1GeometryBasePoint

/-- Complete binary coordinates of this literal actual source point. -/
theorem monsterCo1GeometryVectorPoint72_binary :
    monsterCo1GeometryVectorPoint72.val =
      ![0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0] := by
  change co1BinaryAction monsterCo1GeometryVectorPoint72Transport monsterCo1GeometryBasePoint.val =
      _
  rw [monsterCo1GeometryVectorPoint72Transport_binary, monsterCo1GeometryBasePoint_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
