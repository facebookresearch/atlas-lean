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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint051
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint073

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The literal actual two-core word for source point 118. -/
def monsterCo1GeometryVectorPoint118Transport : Co1 :=
  monsterCo1GeometryVectorPoint51Transport * monsterCo1GeometryTransportOperator 5 *
    monsterCo1GeometryVectorPoint51Transport⁻¹ * monsterCo1GeometryVectorPoint73Transport

/-- Complete displayed binary matrix of actual transport 118. -/
def monsterCo1GeometryVectorPoint118Matrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![623459, 11198030, 11164574, 942723, 472610, 25990, 8414694, 8867859, 8901748, 8859685,
      8422839, 3520921, 471172, 2113546, 2147034, 8423153, 8621503, 11769776, 6867428, 3402644,
      15697015, 14026607, 6178647, 8421639]

/-- First complete finite matrix product in literal actual transport 118. -/
def monsterCo1GeometryVectorPoint118AfterSignMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![328320, 5242317, 13622624, 1034189, 8435104, 49232, 49392, 8419232, 29264, 45808, 8192,
      9828397, 8397872, 8392736, 8401952, 9248, 2106860, 3732692, 2946168, 3155820, 10785204,
      11817880, 5305902, 8397824]

/-- Second complete finite matrix product in literal actual transport 118. -/
def monsterCo1GeometryVectorPoint118AfterInverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![3735793, 15256670, 6860744, 10970174, 8426896, 8422320, 8422352, 8418960, 5904, 63360,
      8415120, 5218410, 5008, 8429568, 41872, 8446864, 6273325, 8558096, 8680832, 7297613,
      7818333, 8277165, 7988064, 25488]

set_option maxHeartbeats 24000000 in
-- Check every entry of this finite actual transport matrix in the Lean kernel.
/-- Every column of transport 118 is its actual Conway binary action. -/
theorem monsterCo1GeometryVectorPoint118Transport_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint118Transport v =
      monsterCo1GeometryVectorPoint118Matrix *ᵥ v := by
  have hx : monsterCo1GeometryVectorPoint51Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![327820, 5176519, 5168842, 1033288, 46144, 8438480, 8438384, 29888, 28976, 45840, 8397472,
    9763490, 8398480, 4096, 8402592, 8398464, 10495878, 12122004, 11335096, 11543946, 2396210,
    3428370, 5306018, 9888] := by decide +kernel
  have hxi : monsterCo1GeometryVectorPoint51InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![12150630, 16329981, 10413664, 11003232, 36864, 57344, 8450880, 57440, 8390304, 1008,
    25600, 12976381, 8192, 8415120, 12336, 53440, 3539809, 13897028, 1040384, 13270269,
    3145968, 15092797, 650493, 8413184] := by decide +kernel
  have hy : monsterCo1GeometryVectorPoint73Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![8388609, 11003449, 11002462, 8906259, 8388736, 8445968, 57456, 57584, 8415040, 8389968,
    8389632, 11601278, 8893156, 2115580, 2114715, 8390470, 6471477, 11805554, 7338855, 6020157,
    8388842, 3145872, 14107252, 8388784] := by rfl
  have he : monsterCo1GeometryVectorPoint118AfterSignMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![328320, 5242317, 13622624, 1034189, 8435104, 49232, 49392, 8419232, 29264, 45808, 8192,
    9828397, 8397872, 8392736, 8401952, 9248, 2106860, 3732692, 2946168, 3155820, 10785204,
    11817880, 5305902, 8397824] := by rfl
  have hf : monsterCo1GeometryVectorPoint118AfterInverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![3735793, 15256670, 6860744, 10970174, 8426896, 8422320, 8422352, 8418960, 5904, 63360,
    8415120, 5218410, 5008, 8429568, 41872, 8446864, 6273325, 8558096, 8680832, 7297613,
    7818333, 8277165, 7988064, 25488] := by rfl
  have hc : monsterCo1GeometryVectorPoint118Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![623459, 11198030, 11164574, 942723, 472610, 25990, 8414694, 8867859, 8901748, 8859685,
    8422839, 3520921, 471172, 2113546, 2147034, 8423153, 8621503, 11769776, 6867428, 3402644,
    15697015, 14026607, 6178647, 8421639] := by rfl
  have hc1 : monsterCo1GeometryVectorPoint51Matrix *
    monsterCo1GeometryTransportOperatorMatrix 5 =
    monsterCo1GeometryVectorPoint118AfterSignMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![327820, 5176519, 5168842, 1033288, 46144, 8438480, 8438384, 29888, 28976, 45840, 8397472,
    9763490, 8398480, 4096, 8402592, 8398464, 10495878, 12122004, 11335096, 11543946, 2396210,
    3428370, 5306018, 9888]
      (monsterCo1GeometryBinaryOperatorMasks 5)
    ![328320, 5242317, 13622624, 1034189, 8435104, 49232, 49392, 8419232, 29264, 45808, 8192,
    9828397, 8397872, 8392736, 8401952, 9248, 2106860, 3732692, 2946168, 3155820, 10785204,
    11817880, 5305902, 8397824] hx (monsterCo1GeometryBinaryOperatorMasks_decode 5) he (by
    decide +kernel)
  have hc2 : monsterCo1GeometryVectorPoint118AfterSignMatrix *
    monsterCo1GeometryVectorPoint51InverseMatrix =
    monsterCo1GeometryVectorPoint118AfterInverseMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![328320, 5242317, 13622624, 1034189, 8435104, 49232, 49392, 8419232, 29264, 45808, 8192,
    9828397, 8397872, 8392736, 8401952, 9248, 2106860, 3732692, 2946168, 3155820, 10785204,
    11817880, 5305902, 8397824]
    ![12150630, 16329981, 10413664, 11003232, 36864, 57344, 8450880, 57440, 8390304, 1008,
    25600, 12976381, 8192, 8415120, 12336, 53440, 3539809, 13897028, 1040384, 13270269,
    3145968, 15092797, 650493, 8413184]
    ![3735793, 15256670, 6860744, 10970174, 8426896, 8422320, 8422352, 8418960, 5904, 63360,
    8415120, 5218410, 5008, 8429568, 41872, 8446864, 6273325, 8558096, 8680832, 7297613,
    7818333, 8277165, 7988064, 25488] he hxi hf (by decide +kernel)
  have hc3 : monsterCo1GeometryVectorPoint118AfterInverseMatrix *
    monsterCo1GeometryVectorPoint73Matrix = monsterCo1GeometryVectorPoint118Matrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![3735793, 15256670, 6860744, 10970174, 8426896, 8422320, 8422352, 8418960, 5904, 63360,
    8415120, 5218410, 5008, 8429568, 41872, 8446864, 6273325, 8558096, 8680832, 7297613,
    7818333, 8277165, 7988064, 25488]
    ![8388609, 11003449, 11002462, 8906259, 8388736, 8445968, 57456, 57584, 8415040, 8389968,
    8389632, 11601278, 8893156, 2115580, 2114715, 8390470, 6471477, 11805554, 7338855, 6020157,
    8388842, 3145872, 14107252, 8388784]
    ![623459, 11198030, 11164574, 942723, 472610, 25990, 8414694, 8867859, 8901748, 8859685,
    8422839, 3520921, 471172, 2113546, 2147034, 8423153, 8621503, 11769776, 6867428, 3402644,
    15697015, 14026607, 6178647, 8421639] hf hy hc (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_line_products
    monsterCo1GeometryVectorPoint51Transport monsterCo1GeometryVectorPoint73Transport 5
    monsterCo1GeometryVectorPoint51Matrix monsterCo1GeometryVectorPoint51InverseMatrix
    monsterCo1GeometryVectorPoint73Matrix
    monsterCo1GeometryVectorPoint118AfterSignMatrix
    monsterCo1GeometryVectorPoint118AfterInverseMatrix monsterCo1GeometryVectorPoint118Matrix
    monsterCo1GeometryVectorPoint51Transport_binary
    monsterCo1GeometryVectorPoint51Transport_inverse_binary
    monsterCo1GeometryVectorPoint73Transport_binary
    hc1 hc2 hc3 v

/-- Source point 118 is the literal actual transported frame point. -/
def monsterCo1GeometryVectorPoint118 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryVectorPoint118Transport • monsterCo1GeometryBasePoint

/-- Complete binary coordinates of this literal actual source point. -/
theorem monsterCo1GeometryVectorPoint118_binary :
    monsterCo1GeometryVectorPoint118.val =
      ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0] := by
  change co1BinaryAction monsterCo1GeometryVectorPoint118Transport monsterCo1GeometryBasePoint.val =
      _
  rw [monsterCo1GeometryVectorPoint118Transport_binary, monsterCo1GeometryBasePoint_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
