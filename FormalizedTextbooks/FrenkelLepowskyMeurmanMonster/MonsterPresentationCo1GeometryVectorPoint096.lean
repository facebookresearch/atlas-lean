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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint030
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint048

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The literal actual two-core word for source point 96. -/
def monsterCo1GeometryVectorPoint96Transport : Co1 :=
  monsterCo1GeometryVectorPoint30Transport * monsterCo1GeometryTransportOperator 4 *
    monsterCo1GeometryVectorPoint30Transport⁻¹ * monsterCo1GeometryVectorPoint48Transport

/-- Complete displayed binary matrix of actual transport 96. -/
def monsterCo1GeometryVectorPoint96Matrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![128, 13691598, 12635343, 58593, 5279471, 9488081, 9487985, 5262959, 6318398, 7383838,
      9446048, 12588033, 6287988, 12901550, 12900355, 328705, 3154570, 2299536, 3282608,
      2105990, 9747344, 9730480, 1117356, 58368]

/-- First complete finite matrix product in literal actual transport 96. -/
def monsterCo1GeometryVectorPoint96AfterSignMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![8388800, 63424, 8451264, 8419232, 57520, 32, 8388640, 57440, 8439600, 8439104, 8388768,
      12615687, 349736, 9463562, 9461927, 8390604, 3211270, 6805867, 15325549, 11600309,
      3203174, 11591680, 12334415, 8389632]

/-- Second complete finite matrix product in literal actual transport 96. -/
def monsterCo1GeometryVectorPoint96AfterInverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![1, 8388610, 8388612, 8388616, 16, 32, 64, 128, 8388864, 8389120, 1024, 3205120, 5888,
      8432, 16528, 32864, 65638, 131226, 262298, 524390, 1049601, 2098177, 4195073, 8388608]

set_option maxHeartbeats 24000000 in
-- Check every entry of this finite actual transport matrix in the Lean kernel.
/-- Every column of transport 96 is its actual Conway binary action. -/
theorem monsterCo1GeometryVectorPoint96Transport_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint96Transport v =
      monsterCo1GeometryVectorPoint96Matrix *ᵥ v := by
  have hx : monsterCo1GeometryVectorPoint30Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![8388800, 8451008, 61632, 29600, 57520, 32, 8388640, 57440, 49968, 49472, 8388768,
    12615680, 8738040, 1075162, 9461879, 1996, 3212038, 15161819, 6904285, 11600565, 3203078,
    11591776, 3946495, 8389632] := by decide +kernel
  have hxi : monsterCo1GeometryVectorPoint30InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![58465, 648966, 3793767, 12149504, 241, 32, 1057, 1088, 1942, 2032, 8388704, 12860069,
    1252, 1334, 1500, 1131, 1115367, 6260357, 2651759, 4322539, 3187834, 1090714, 3083, 96] :=
    by decide +kernel
  have hy : monsterCo1GeometryVectorPoint48Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![128, 13635278, 12593359, 225, 5279471, 9488081, 9487985, 5262959, 6327614, 7360286,
    9446048, 12965517, 14619380, 12852366, 12851331, 328865, 2098219, 15980607, 14866463,
    3146791, 301488, 285584, 118284, 58368] := by decide +kernel
  have he : monsterCo1GeometryVectorPoint96AfterSignMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![8388800, 63424, 8451264, 8419232, 57520, 32, 8388640, 57440, 8439600, 8439104, 8388768,
    12615687, 349736, 9463562, 9461927, 8390604, 3211270, 6805867, 15325549, 11600309, 3203174,
    11591680, 12334415, 8389632] := by rfl
  have hf : monsterCo1GeometryVectorPoint96AfterInverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![1, 8388610, 8388612, 8388616, 16, 32, 64, 128, 8388864, 8389120, 1024, 3205120, 5888,
    8432, 16528, 32864, 65638, 131226, 262298, 524390, 1049601, 2098177, 4195073, 8388608] :=
    by decide +kernel
  have hc : monsterCo1GeometryVectorPoint96Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![128, 13691598, 12635343, 58593, 5279471, 9488081, 9487985, 5262959, 6318398, 7383838,
    9446048, 12588033, 6287988, 12901550, 12900355, 328705, 3154570, 2299536, 3282608, 2105990,
    9747344, 9730480, 1117356, 58368] := by rfl
  have hc1 : monsterCo1GeometryVectorPoint30Matrix *
    monsterCo1GeometryTransportOperatorMatrix 4 =
    monsterCo1GeometryVectorPoint96AfterSignMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![8388800, 8451008, 61632, 29600, 57520, 32, 8388640, 57440, 49968, 49472, 8388768,
    12615680, 8738040, 1075162, 9461879, 1996, 3212038, 15161819, 6904285, 11600565, 3203078,
    11591776, 3946495, 8389632]
      (monsterCo1GeometryBinaryOperatorMasks 4)
    ![8388800, 63424, 8451264, 8419232, 57520, 32, 8388640, 57440, 8439600, 8439104, 8388768,
    12615687, 349736, 9463562, 9461927, 8390604, 3211270, 6805867, 15325549, 11600309, 3203174,
    11591680, 12334415, 8389632] hx (monsterCo1GeometryBinaryOperatorMasks_decode 4) he (by
    decide +kernel)
  have hc2 : monsterCo1GeometryVectorPoint96AfterSignMatrix *
    monsterCo1GeometryVectorPoint30InverseMatrix =
    monsterCo1GeometryVectorPoint96AfterInverseMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![8388800, 63424, 8451264, 8419232, 57520, 32, 8388640, 57440, 8439600, 8439104, 8388768,
    12615687, 349736, 9463562, 9461927, 8390604, 3211270, 6805867, 15325549, 11600309, 3203174,
    11591680, 12334415, 8389632]
    ![58465, 648966, 3793767, 12149504, 241, 32, 1057, 1088, 1942, 2032, 8388704, 12860069,
    1252, 1334, 1500, 1131, 1115367, 6260357, 2651759, 4322539, 3187834, 1090714, 3083, 96]
    ![1, 8388610, 8388612, 8388616, 16, 32, 64, 128, 8388864, 8389120, 1024, 3205120, 5888,
    8432, 16528, 32864, 65638, 131226, 262298, 524390, 1049601, 2098177, 4195073, 8388608] he
    hxi hf (by decide +kernel)
  have hc3 : monsterCo1GeometryVectorPoint96AfterInverseMatrix *
    monsterCo1GeometryVectorPoint48Matrix = monsterCo1GeometryVectorPoint96Matrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![1, 8388610, 8388612, 8388616, 16, 32, 64, 128, 8388864, 8389120, 1024, 3205120, 5888,
    8432, 16528, 32864, 65638, 131226, 262298, 524390, 1049601, 2098177, 4195073, 8388608]
    ![128, 13635278, 12593359, 225, 5279471, 9488081, 9487985, 5262959, 6327614, 7360286,
    9446048, 12965517, 14619380, 12852366, 12851331, 328865, 2098219, 15980607, 14866463,
    3146791, 301488, 285584, 118284, 58368]
    ![128, 13691598, 12635343, 58593, 5279471, 9488081, 9487985, 5262959, 6318398, 7383838,
    9446048, 12588033, 6287988, 12901550, 12900355, 328705, 3154570, 2299536, 3282608, 2105990,
    9747344, 9730480, 1117356, 58368] hf hy hc (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_line_products
    monsterCo1GeometryVectorPoint30Transport monsterCo1GeometryVectorPoint48Transport 4
    monsterCo1GeometryVectorPoint30Matrix monsterCo1GeometryVectorPoint30InverseMatrix
    monsterCo1GeometryVectorPoint48Matrix
    monsterCo1GeometryVectorPoint96AfterSignMatrix
    monsterCo1GeometryVectorPoint96AfterInverseMatrix monsterCo1GeometryVectorPoint96Matrix
    monsterCo1GeometryVectorPoint30Transport_binary
    monsterCo1GeometryVectorPoint30Transport_inverse_binary
    monsterCo1GeometryVectorPoint48Transport_binary
    hc1 hc2 hc3 v

/-- Source point 96 is the literal actual transported frame point. -/
def monsterCo1GeometryVectorPoint96 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryVectorPoint96Transport • monsterCo1GeometryBasePoint

/-- Complete binary coordinates of this literal actual source point. -/
theorem monsterCo1GeometryVectorPoint96_binary :
    monsterCo1GeometryVectorPoint96.val =
      ![0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 1, 1, 0] := by
  change co1BinaryAction monsterCo1GeometryVectorPoint96Transport monsterCo1GeometryBasePoint.val =
      _
  rw [monsterCo1GeometryVectorPoint96Transport_binary, monsterCo1GeometryBasePoint_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
