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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint044
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint081

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The literal actual two-core word for source point 128. -/
def monsterCo1GeometryVectorPoint128Transport : Co1 :=
  monsterCo1GeometryVectorPoint44Transport * monsterCo1GeometryTransportOperator 5 *
    monsterCo1GeometryVectorPoint44Transport⁻¹ * monsterCo1GeometryVectorPoint81Transport

/-- Complete displayed binary matrix of actual transport 128. -/
def monsterCo1GeometryVectorPoint128Matrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![9319461, 950997, 5815413, 14170565, 8892482, 8414096, 8859685, 8415040, 504565, 57584,
      34560, 4875499, 8894004, 58294, 2106299, 2105532, 13740517, 4578394, 12708143, 16561898,
      2004744, 11589780, 9577173, 33712]

/-- First complete finite matrix product in literal actual transport 128. -/
def monsterCo1GeometryVectorPoint128AfterSignMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![12517811, 11142035, 5557416, 5507620, 5424, 13248, 8441984, 12288, 8442528, 12928,
      8438400, 9813032, 8401600, 8401472, 8423040, 17024, 78176, 1119632, 8569875, 7798221,
      8636080, 7486287, 4194315, 50816]

/-- Second complete finite matrix product in literal actual transport 128. -/
def monsterCo1GeometryVectorPoint128AfterInverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![9814145, 9814530, 9711944, 9712580, 13264, 672, 8450944, 512, 8450752, 128, 1664,
      1374380, 4736, 8832, 8421856, 8405856, 66176, 8520652, 1163308, 16226359, 376876,
      6268987, 4194304, 8389248]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 24000000 in
-- Check every entry of this finite actual transport matrix in the Lean kernel.
/-- Every column of transport 128 is its actual Conway binary action. -/
theorem monsterCo1GeometryVectorPoint128Transport_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint128Transport v =
      monsterCo1GeometryVectorPoint128Matrix *ᵥ v := by
  have hx : monsterCo1GeometryVectorPoint44Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![4129008, 2752592, 5622951, 5572779, 5392, 12608, 53792, 12928, 53248, 12288, 8437760,
    1359687, 8400960, 8401088, 34272, 8405856, 78816, 1119548, 181916, 7864199, 246847,
    7551369, 4194315, 50176] := by decide +kernel
  have hxi : monsterCo1GeometryVectorPoint44InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![12518067, 11141779, 5523912, 13912516, 54192, 13248, 8441984, 12288, 8442528, 12928,
    50816, 4194315, 8439680, 8439168, 8405472, 34656, 78176, 315708, 8531999, 578262, 8585916,
    9175256, 8473060, 8438400] := by decide +kernel
  have hy : monsterCo1GeometryVectorPoint81Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![1040, 13648, 4864, 4352, 57504, 58400, 57456, 57584, 8413856, 8415040, 8388784, 9620777,
    471428, 8414214, 10495244, 2138555, 5320277, 12967738, 13622218, 5986653, 1091053, 1074337,
    9577173, 8389632] := by rfl
  have he : monsterCo1GeometryVectorPoint128AfterSignMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![12517811, 11142035, 5557416, 5507620, 5424, 13248, 8441984, 12288, 8442528, 12928,
    8438400, 9813032, 8401600, 8401472, 8423040, 17024, 78176, 1119632, 8569875, 7798221,
    8636080, 7486287, 4194315, 50816] := by rfl
  have hf : monsterCo1GeometryVectorPoint128AfterInverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![9814145, 9814530, 9711944, 9712580, 13264, 672, 8450944, 512, 8450752, 128, 1664,
    1374380, 4736, 8832, 8421856, 8405856, 66176, 8520652, 1163308, 16226359, 376876, 6268987,
    4194304, 8389248] := by rfl
  have hc : monsterCo1GeometryVectorPoint128Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![9319461, 950997, 5815413, 14170565, 8892482, 8414096, 8859685, 8415040, 504565, 57584,
    34560, 4875499, 8894004, 58294, 2106299, 2105532, 13740517, 4578394, 12708143, 16561898,
    2004744, 11589780, 9577173, 33712] := by rfl
  have hc1 : monsterCo1GeometryVectorPoint44Matrix *
    monsterCo1GeometryTransportOperatorMatrix 5 =
    monsterCo1GeometryVectorPoint128AfterSignMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![4129008, 2752592, 5622951, 5572779, 5392, 12608, 53792, 12928, 53248, 12288, 8437760,
    1359687, 8400960, 8401088, 34272, 8405856, 78816, 1119548, 181916, 7864199, 246847,
    7551369, 4194315, 50176]
      (monsterCo1GeometryBinaryOperatorMasks 5)
    ![12517811, 11142035, 5557416, 5507620, 5424, 13248, 8441984, 12288, 8442528, 12928,
    8438400, 9813032, 8401600, 8401472, 8423040, 17024, 78176, 1119632, 8569875, 7798221,
    8636080, 7486287, 4194315, 50816] hx (monsterCo1GeometryBinaryOperatorMasks_decode 5) he
    (by decide +kernel)
  have hc2 : monsterCo1GeometryVectorPoint128AfterSignMatrix *
    monsterCo1GeometryVectorPoint44InverseMatrix =
    monsterCo1GeometryVectorPoint128AfterInverseMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![12517811, 11142035, 5557416, 5507620, 5424, 13248, 8441984, 12288, 8442528, 12928,
    8438400, 9813032, 8401600, 8401472, 8423040, 17024, 78176, 1119632, 8569875, 7798221,
    8636080, 7486287, 4194315, 50816]
    ![12518067, 11141779, 5523912, 13912516, 54192, 13248, 8441984, 12288, 8442528, 12928,
    50816, 4194315, 8439680, 8439168, 8405472, 34656, 78176, 315708, 8531999, 578262, 8585916,
    9175256, 8473060, 8438400]
    ![9814145, 9814530, 9711944, 9712580, 13264, 672, 8450944, 512, 8450752, 128, 1664,
    1374380, 4736, 8832, 8421856, 8405856, 66176, 8520652, 1163308, 16226359, 376876, 6268987,
    4194304, 8389248] he hxi hf (by decide +kernel)
  have hc3 : monsterCo1GeometryVectorPoint128AfterInverseMatrix *
    monsterCo1GeometryVectorPoint81Matrix = monsterCo1GeometryVectorPoint128Matrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![9814145, 9814530, 9711944, 9712580, 13264, 672, 8450944, 512, 8450752, 128, 1664,
    1374380, 4736, 8832, 8421856, 8405856, 66176, 8520652, 1163308, 16226359, 376876, 6268987,
    4194304, 8389248]
    ![1040, 13648, 4864, 4352, 57504, 58400, 57456, 57584, 8413856, 8415040, 8388784, 9620777,
    471428, 8414214, 10495244, 2138555, 5320277, 12967738, 13622218, 5986653, 1091053, 1074337,
    9577173, 8389632]
    ![9319461, 950997, 5815413, 14170565, 8892482, 8414096, 8859685, 8415040, 504565, 57584,
    34560, 4875499, 8894004, 58294, 2106299, 2105532, 13740517, 4578394, 12708143, 16561898,
    2004744, 11589780, 9577173, 33712] hf hy hc (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_line_products
    monsterCo1GeometryVectorPoint44Transport monsterCo1GeometryVectorPoint81Transport 5
    monsterCo1GeometryVectorPoint44Matrix monsterCo1GeometryVectorPoint44InverseMatrix
    monsterCo1GeometryVectorPoint81Matrix
    monsterCo1GeometryVectorPoint128AfterSignMatrix
    monsterCo1GeometryVectorPoint128AfterInverseMatrix monsterCo1GeometryVectorPoint128Matrix
    monsterCo1GeometryVectorPoint44Transport_binary
    monsterCo1GeometryVectorPoint44Transport_inverse_binary
    monsterCo1GeometryVectorPoint81Transport_binary
    hc1 hc2 hc3 v

/-- Source point 128 is the literal actual transported frame point. -/
def monsterCo1GeometryVectorPoint128 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryVectorPoint128Transport • monsterCo1GeometryBasePoint

/-- Complete binary coordinates of this literal actual source point. -/
theorem monsterCo1GeometryVectorPoint128_binary :
    monsterCo1GeometryVectorPoint128.val =
      ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 1, 0, 0] := by
  change co1BinaryAction monsterCo1GeometryVectorPoint128Transport monsterCo1GeometryBasePoint.val =
      _
  rw [monsterCo1GeometryVectorPoint128Transport_binary, monsterCo1GeometryBasePoint_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
