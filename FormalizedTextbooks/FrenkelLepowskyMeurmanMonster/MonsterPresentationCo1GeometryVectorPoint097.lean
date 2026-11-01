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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint042
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint049

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The literal actual two-core word for source point 97. -/
def monsterCo1GeometryVectorPoint97Transport : Co1 :=
  monsterCo1GeometryVectorPoint42Transport * monsterCo1GeometryTransportOperator 1 *
    monsterCo1GeometryVectorPoint42Transport⁻¹ * monsterCo1GeometryVectorPoint49Transport

/-- Complete displayed binary matrix of actual transport 97. -/
def monsterCo1GeometryVectorPoint97Matrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![327820, 5167719, 5168842, 1033288, 46144, 8438480, 8438384, 29888, 28976, 45840, 8397472,
      13693100, 8848, 4096, 12960, 8832, 2105990, 3731604, 2945208, 3154570, 10757666,
      11806242, 1371308, 9888]

/-- First complete finite matrix product in literal actual transport 97. -/
def monsterCo1GeometryVectorPoint97AfterSignMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![128, 8450752, 8442048, 8447200, 8427232, 8438480, 8438384, 8410720, 28976, 45840, 9888,
      265216, 9421013, 12855470, 12848803, 337569, 2098219, 15980607, 14866463, 3146791,
      2368047, 3416623, 13752845, 8389632]

/-- Second complete finite matrix product in literal actual transport 97. -/
def monsterCo1GeometryVectorPoint97AfterInverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![1, 8388610, 4, 8388616, 8388624, 32, 64, 8388736, 256, 512, 8389632, 4828407, 8392750,
      8398845, 8405915, 33799, 8454854, 8520323, 8651026, 8913206, 1049286, 2097462, 12582922,
      8388608]

set_option maxHeartbeats 24000000 in
-- Check every entry of this finite actual transport matrix in the Lean kernel.
/-- Every column of transport 97 is its actual Conway binary action. -/
theorem monsterCo1GeometryVectorPoint97Transport_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint97Transport v =
      monsterCo1GeometryVectorPoint97Matrix *ᵥ v := by
  have hx : monsterCo1GeometryVectorPoint42Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![128, 63168, 8442048, 57568, 37600, 8438480, 8438384, 21088, 28976, 45840, 8397472,
    269326, 1032421, 4471982, 4464291, 336513, 10487083, 7588623, 6473999, 11536167, 2369327,
    3417391, 5359661, 8389632] := by decide +kernel
  have hxi : monsterCo1GeometryVectorPoint42InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![12148742, 7381770, 2024545, 2614369, 1065, 97, 8389391, 1, 1696, 1008, 1126, 4606096,
    2045, 8389622, 8390627, 8390514, 3538944, 6129559, 1040385, 4452367, 3146736, 7283116,
    8399766, 8389734] := by decide +kernel
  have hy : monsterCo1GeometryVectorPoint49Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![327820, 5176519, 5168842, 1041128, 37600, 8438480, 8438384, 21088, 28976, 45840, 8389632,
    5359661, 9373189, 12848142, 4458499, 8717313, 10487083, 7588623, 6473999, 11536167,
    2369327, 3417391, 5624867, 9888] := by decide +kernel
  have he : monsterCo1GeometryVectorPoint97AfterSignMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![128, 8450752, 8442048, 8447200, 8427232, 8438480, 8438384, 8410720, 28976, 45840, 9888,
    265216, 9421013, 12855470, 12848803, 337569, 2098219, 15980607, 14866463, 3146791, 2368047,
    3416623, 13752845, 8389632] := by rfl
  have hf : monsterCo1GeometryVectorPoint97AfterInverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![1, 8388610, 4, 8388616, 8388624, 32, 64, 8388736, 256, 512, 8389632, 4828407, 8392750,
    8398845, 8405915, 33799, 8454854, 8520323, 8651026, 8913206, 1049286, 2097462, 12582922,
    8388608] := by rfl
  have hc : monsterCo1GeometryVectorPoint97Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![327820, 5167719, 5168842, 1033288, 46144, 8438480, 8438384, 29888, 28976, 45840, 8397472,
    13693100, 8848, 4096, 12960, 8832, 2105990, 3731604, 2945208, 3154570, 10757666, 11806242,
    1371308, 9888] := by rfl
  have hc1 : monsterCo1GeometryVectorPoint42Matrix *
    monsterCo1GeometryTransportOperatorMatrix 1 =
    monsterCo1GeometryVectorPoint97AfterSignMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![128, 63168, 8442048, 57568, 37600, 8438480, 8438384, 21088, 28976, 45840, 8397472,
    269326, 1032421, 4471982, 4464291, 336513, 10487083, 7588623, 6473999, 11536167, 2369327,
    3417391, 5359661, 8389632]
      (monsterCo1GeometryBinaryOperatorMasks 1)
    ![128, 8450752, 8442048, 8447200, 8427232, 8438480, 8438384, 8410720, 28976, 45840, 9888,
    265216, 9421013, 12855470, 12848803, 337569, 2098219, 15980607, 14866463, 3146791, 2368047,
    3416623, 13752845, 8389632] hx (monsterCo1GeometryBinaryOperatorMasks_decode 1) he (by
    decide +kernel)
  have hc2 : monsterCo1GeometryVectorPoint97AfterSignMatrix *
    monsterCo1GeometryVectorPoint42InverseMatrix =
    monsterCo1GeometryVectorPoint97AfterInverseMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![128, 8450752, 8442048, 8447200, 8427232, 8438480, 8438384, 8410720, 28976, 45840, 9888,
    265216, 9421013, 12855470, 12848803, 337569, 2098219, 15980607, 14866463, 3146791, 2368047,
    3416623, 13752845, 8389632]
    ![12148742, 7381770, 2024545, 2614369, 1065, 97, 8389391, 1, 1696, 1008, 1126, 4606096,
    2045, 8389622, 8390627, 8390514, 3538944, 6129559, 1040385, 4452367, 3146736, 7283116,
    8399766, 8389734]
    ![1, 8388610, 4, 8388616, 8388624, 32, 64, 8388736, 256, 512, 8389632, 4828407, 8392750,
    8398845, 8405915, 33799, 8454854, 8520323, 8651026, 8913206, 1049286, 2097462, 12582922,
    8388608] he hxi hf (by decide +kernel)
  have hc3 : monsterCo1GeometryVectorPoint97AfterInverseMatrix *
    monsterCo1GeometryVectorPoint49Matrix = monsterCo1GeometryVectorPoint97Matrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![1, 8388610, 4, 8388616, 8388624, 32, 64, 8388736, 256, 512, 8389632, 4828407, 8392750,
    8398845, 8405915, 33799, 8454854, 8520323, 8651026, 8913206, 1049286, 2097462, 12582922,
    8388608]
    ![327820, 5176519, 5168842, 1041128, 37600, 8438480, 8438384, 21088, 28976, 45840, 8389632,
    5359661, 9373189, 12848142, 4458499, 8717313, 10487083, 7588623, 6473999, 11536167,
    2369327, 3417391, 5624867, 9888]
    ![327820, 5167719, 5168842, 1033288, 46144, 8438480, 8438384, 29888, 28976, 45840, 8397472,
    13693100, 8848, 4096, 12960, 8832, 2105990, 3731604, 2945208, 3154570, 10757666, 11806242,
    1371308, 9888] hf hy hc (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_line_products
    monsterCo1GeometryVectorPoint42Transport monsterCo1GeometryVectorPoint49Transport 1
    monsterCo1GeometryVectorPoint42Matrix monsterCo1GeometryVectorPoint42InverseMatrix
    monsterCo1GeometryVectorPoint49Matrix
    monsterCo1GeometryVectorPoint97AfterSignMatrix
    monsterCo1GeometryVectorPoint97AfterInverseMatrix monsterCo1GeometryVectorPoint97Matrix
    monsterCo1GeometryVectorPoint42Transport_binary
    monsterCo1GeometryVectorPoint42Transport_inverse_binary
    monsterCo1GeometryVectorPoint49Transport_binary
    hc1 hc2 hc3 v

/-- Source point 97 is the literal actual transported frame point. -/
def monsterCo1GeometryVectorPoint97 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryVectorPoint97Transport • monsterCo1GeometryBasePoint

/-- Complete binary coordinates of this literal actual source point. -/
theorem monsterCo1GeometryVectorPoint97_binary :
    monsterCo1GeometryVectorPoint97.val =
      ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0] := by
  change co1BinaryAction monsterCo1GeometryVectorPoint97Transport monsterCo1GeometryBasePoint.val =
      _
  rw [monsterCo1GeometryVectorPoint97Transport_binary, monsterCo1GeometryBasePoint_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
