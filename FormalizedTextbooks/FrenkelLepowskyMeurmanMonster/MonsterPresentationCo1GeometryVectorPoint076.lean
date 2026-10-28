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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint035

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The literal actual two-core word for source point 76. -/
def monsterCo1GeometryVectorPoint76Transport : Co1 :=
  monsterCo1GeometryVectorPoint30Transport * monsterCo1GeometryTransportOperator 1 *
    monsterCo1GeometryVectorPoint30Transport⁻¹ * monsterCo1GeometryVectorPoint35Transport

/-- Complete displayed binary matrix of actual transport 76. -/
def monsterCo1GeometryVectorPoint76Matrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![8388609, 12647439, 7346190, 14743566, 8445968, 48, 192, 8446016, 24784, 41072, 8389632,
      7339469, 5303871, 9445889, 2146800, 11536128, 11748491, 4349160, 13147381, 12354791,
      3146891, 3146791, 3209742, 8445952]

/-- First complete finite matrix product in literal actual transport 76. -/
def monsterCo1GeometryVectorPoint76AfterSignMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![8388800, 63424, 8451264, 29600, 8447152, 32, 8388640, 8447072, 49968, 49472, 8388768,
      4228110, 348376, 1074650, 1073783, 1996, 3211302, 15158507, 6900989, 3211669, 11593478,
      3204960, 3944703, 8389632]

/-- Second complete finite matrix product in literal actual transport 76. -/
def monsterCo1GeometryVectorPoint76AfterInverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![1, 8388610, 8388612, 8, 8388624, 32, 64, 8388736, 256, 512, 1024, 618337, 8392736, 10224,
      18320, 32768, 65606, 8520643, 8651570, 524326, 9437286, 10485862, 12582918, 8388608]

set_option maxHeartbeats 24000000 in
-- Check every entry of this finite actual transport matrix in the Lean kernel.
/-- Every column of transport 76 is its actual Conway binary action. -/
theorem monsterCo1GeometryVectorPoint76Transport_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint76Transport v =
      monsterCo1GeometryVectorPoint76Matrix *ᵥ v := by
  have hx : monsterCo1GeometryVectorPoint30Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![8388800, 8451008, 61632, 29600, 57520, 32, 8388640, 57440, 49968, 49472, 8388768,
    12615680, 8738040, 1075162, 9461879, 1996, 3212038, 15161819, 6904285, 11600565, 3203078,
    11591776, 3946495, 8389632] := by decide +kernel
  have hxi : monsterCo1GeometryVectorPoint30InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![58465, 648966, 3793767, 12149504, 241, 32, 1057, 1088, 1942, 2032, 8388704, 12860069,
    1252, 1334, 1500, 1131, 1115367, 6260357, 2651759, 4322539, 3187834, 1090714, 3083, 96] :=
    by decide +kernel
  have hy : monsterCo1GeometryVectorPoint35Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![8388609, 4201487, 15792142, 14743566, 16, 48, 192, 64, 24784, 41072, 8389632, 13638145,
    13635087, 1107457, 10487040, 11536128, 237642, 155846, 565370, 811222, 122, 214, 65039,
    8445952] := by decide +kernel
  have he : monsterCo1GeometryVectorPoint76AfterSignMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![8388800, 63424, 8451264, 29600, 8447152, 32, 8388640, 8447072, 49968, 49472, 8388768,
    4228110, 348376, 1074650, 1073783, 1996, 3211302, 15158507, 6900989, 3211669, 11593478,
    3204960, 3944703, 8389632] := by rfl
  have hf : monsterCo1GeometryVectorPoint76AfterInverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![1, 8388610, 8388612, 8, 8388624, 32, 64, 8388736, 256, 512, 1024, 618337, 8392736, 10224,
    18320, 32768, 65606, 8520643, 8651570, 524326, 9437286, 10485862, 12582918, 8388608] := by rfl
  have hc : monsterCo1GeometryVectorPoint76Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![8388609, 12647439, 7346190, 14743566, 8445968, 48, 192, 8446016, 24784, 41072, 8389632,
    7339469, 5303871, 9445889, 2146800, 11536128, 11748491, 4349160, 13147381, 12354791,
    3146891, 3146791, 3209742, 8445952] := by rfl
  have hc1 : monsterCo1GeometryVectorPoint30Matrix *
    monsterCo1GeometryTransportOperatorMatrix 1 =
    monsterCo1GeometryVectorPoint76AfterSignMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![8388800, 8451008, 61632, 29600, 57520, 32, 8388640, 57440, 49968, 49472, 8388768,
    12615680, 8738040, 1075162, 9461879, 1996, 3212038, 15161819, 6904285, 11600565, 3203078,
    11591776, 3946495, 8389632]
      (monsterCo1GeometryBinaryOperatorMasks 1)
    ![8388800, 63424, 8451264, 29600, 8447152, 32, 8388640, 8447072, 49968, 49472, 8388768,
    4228110, 348376, 1074650, 1073783, 1996, 3211302, 15158507, 6900989, 3211669, 11593478,
    3204960, 3944703, 8389632] hx (monsterCo1GeometryBinaryOperatorMasks_decode 1) he (by
    decide +kernel)
  have hc2 : monsterCo1GeometryVectorPoint76AfterSignMatrix *
    monsterCo1GeometryVectorPoint30InverseMatrix =
    monsterCo1GeometryVectorPoint76AfterInverseMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![8388800, 63424, 8451264, 29600, 8447152, 32, 8388640, 8447072, 49968, 49472, 8388768,
    4228110, 348376, 1074650, 1073783, 1996, 3211302, 15158507, 6900989, 3211669, 11593478,
    3204960, 3944703, 8389632]
    ![58465, 648966, 3793767, 12149504, 241, 32, 1057, 1088, 1942, 2032, 8388704, 12860069,
    1252, 1334, 1500, 1131, 1115367, 6260357, 2651759, 4322539, 3187834, 1090714, 3083, 96]
    ![1, 8388610, 8388612, 8, 8388624, 32, 64, 8388736, 256, 512, 1024, 618337, 8392736, 10224,
    18320, 32768, 65606, 8520643, 8651570, 524326, 9437286, 10485862, 12582918, 8388608] he hxi
    hf (by decide +kernel)
  have hc3 : monsterCo1GeometryVectorPoint76AfterInverseMatrix *
    monsterCo1GeometryVectorPoint35Matrix = monsterCo1GeometryVectorPoint76Matrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![1, 8388610, 8388612, 8, 8388624, 32, 64, 8388736, 256, 512, 1024, 618337, 8392736, 10224,
    18320, 32768, 65606, 8520643, 8651570, 524326, 9437286, 10485862, 12582918, 8388608]
    ![8388609, 4201487, 15792142, 14743566, 16, 48, 192, 64, 24784, 41072, 8389632, 13638145,
    13635087, 1107457, 10487040, 11536128, 237642, 155846, 565370, 811222, 122, 214, 65039,
    8445952]
    ![8388609, 12647439, 7346190, 14743566, 8445968, 48, 192, 8446016, 24784, 41072, 8389632,
    7339469, 5303871, 9445889, 2146800, 11536128, 11748491, 4349160, 13147381, 12354791,
    3146891, 3146791, 3209742, 8445952] hf hy hc (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_line_products
    monsterCo1GeometryVectorPoint30Transport monsterCo1GeometryVectorPoint35Transport 1
    monsterCo1GeometryVectorPoint30Matrix monsterCo1GeometryVectorPoint30InverseMatrix
    monsterCo1GeometryVectorPoint35Matrix
    monsterCo1GeometryVectorPoint76AfterSignMatrix
    monsterCo1GeometryVectorPoint76AfterInverseMatrix monsterCo1GeometryVectorPoint76Matrix
    monsterCo1GeometryVectorPoint30Transport_binary
    monsterCo1GeometryVectorPoint30Transport_inverse_binary
    monsterCo1GeometryVectorPoint35Transport_binary
    hc1 hc2 hc3 v

/-- Source point 76 is the literal actual transported frame point. -/
def monsterCo1GeometryVectorPoint76 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryVectorPoint76Transport • monsterCo1GeometryBasePoint

/-- Complete binary coordinates of this literal actual source point. -/
theorem monsterCo1GeometryVectorPoint76_binary :
    monsterCo1GeometryVectorPoint76.val =
      ![0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0] := by
  change co1BinaryAction monsterCo1GeometryVectorPoint76Transport monsterCo1GeometryBasePoint.val =
      _
  rw [monsterCo1GeometryVectorPoint76Transport_binary, monsterCo1GeometryBasePoint_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
