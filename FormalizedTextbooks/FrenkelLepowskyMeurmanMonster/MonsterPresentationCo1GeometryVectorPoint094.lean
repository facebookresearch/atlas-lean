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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint046

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The literal actual two-core word for source point 94. -/
def monsterCo1GeometryVectorPoint94Transport : Co1 :=
  monsterCo1GeometryVectorPoint30Transport * monsterCo1GeometryTransportOperator 2 *
    monsterCo1GeometryVectorPoint30Transport⁻¹ * monsterCo1GeometryVectorPoint46Transport

/-- Complete displayed binary matrix of actual transport 94. -/
def monsterCo1GeometryVectorPoint94Matrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![4129584, 11203280, 9819692, 9773612, 12572128, 12575904, 12575824, 12572368, 12646839,
      12598907, 12518640, 5209005, 12830260, 12382851, 792094, 11592797, 3115132, 13735735,
      6443559, 10455264, 8605843, 235427, 16520839, 50176]

/-- First complete finite matrix product in literal actual transport 94. -/
def monsterCo1GeometryVectorPoint94AfterSignMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![8388800, 63424, 8451264, 29600, 57520, 32, 8388640, 57440, 49968, 49472, 8388768,
      4228109, 8738040, 1074042, 9462999, 1996, 11600214, 6781147, 6912637, 11600101, 11591926,
      11591824, 3944703, 8389632]

/-- Second complete finite matrix product in literal actual transport 94. -/
def monsterCo1GeometryVectorPoint94AfterInverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![1, 8388610, 8388612, 8, 16, 32, 64, 128, 256, 512, 1024, 27654, 4096, 8397824, 8406016,
      32768, 66368, 131776, 262448, 525088, 1048784, 2097328, 12582918, 8388608]

set_option maxHeartbeats 24000000 in
-- Check every entry of this finite actual transport matrix in the Lean kernel.
/-- Every column of transport 94 is its actual Conway binary action. -/
theorem monsterCo1GeometryVectorPoint94Transport_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint94Transport v =
      monsterCo1GeometryVectorPoint94Matrix *ᵥ v := by
  have hx : monsterCo1GeometryVectorPoint30Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![8388800, 8451008, 61632, 29600, 57520, 32, 8388640, 57440, 49968, 49472, 8388768,
    12615680, 8738040, 1075162, 9461879, 1996, 3212038, 15161819, 6904285, 11600565, 3203078,
    11591776, 3946495, 8389632] := by decide +kernel
  have hxi : monsterCo1GeometryVectorPoint30InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![58465, 648966, 3793767, 12149504, 241, 32, 1057, 1088, 1942, 2032, 8388704, 12860069,
    1252, 1334, 1500, 1131, 1115367, 6260357, 2651759, 4322539, 3187834, 1090714, 3083, 96] :=
    by decide +kernel
  have hy : monsterCo1GeometryVectorPoint46Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![4129584, 11155152, 9769516, 9773612, 12572128, 12575904, 12575824, 12572368, 12646839,
    12598907, 12518640, 8372028, 12830260, 209523, 11785966, 11592797, 9481184, 1153996,
    10656464, 2141068, 3979251, 12349491, 12842619, 50176] := by decide +kernel
  have he : monsterCo1GeometryVectorPoint94AfterSignMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![8388800, 63424, 8451264, 29600, 57520, 32, 8388640, 57440, 49968, 49472, 8388768,
    4228109, 8738040, 1074042, 9462999, 1996, 11600214, 6781147, 6912637, 11600101, 11591926,
    11591824, 3944703, 8389632] := by rfl
  have hf : monsterCo1GeometryVectorPoint94AfterInverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![1, 8388610, 8388612, 8, 16, 32, 64, 128, 256, 512, 1024, 27654, 4096, 8397824, 8406016,
    32768, 66368, 131776, 262448, 525088, 1048784, 2097328, 12582918, 8388608] := by rfl
  have hc : monsterCo1GeometryVectorPoint94Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![4129584, 11203280, 9819692, 9773612, 12572128, 12575904, 12575824, 12572368, 12646839,
    12598907, 12518640, 5209005, 12830260, 12382851, 792094, 11592797, 3115132, 13735735,
    6443559, 10455264, 8605843, 235427, 16520839, 50176] := by rfl
  have hc1 : monsterCo1GeometryVectorPoint30Matrix *
    monsterCo1GeometryTransportOperatorMatrix 2 =
    monsterCo1GeometryVectorPoint94AfterSignMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![8388800, 8451008, 61632, 29600, 57520, 32, 8388640, 57440, 49968, 49472, 8388768,
    12615680, 8738040, 1075162, 9461879, 1996, 3212038, 15161819, 6904285, 11600565, 3203078,
    11591776, 3946495, 8389632]
      (monsterCo1GeometryBinaryOperatorMasks 2)
    ![8388800, 63424, 8451264, 29600, 57520, 32, 8388640, 57440, 49968, 49472, 8388768,
    4228109, 8738040, 1074042, 9462999, 1996, 11600214, 6781147, 6912637, 11600101, 11591926,
    11591824, 3944703, 8389632] hx (monsterCo1GeometryBinaryOperatorMasks_decode 2) he (by
    decide +kernel)
  have hc2 : monsterCo1GeometryVectorPoint94AfterSignMatrix *
    monsterCo1GeometryVectorPoint30InverseMatrix =
    monsterCo1GeometryVectorPoint94AfterInverseMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![8388800, 63424, 8451264, 29600, 57520, 32, 8388640, 57440, 49968, 49472, 8388768,
    4228109, 8738040, 1074042, 9462999, 1996, 11600214, 6781147, 6912637, 11600101, 11591926,
    11591824, 3944703, 8389632]
    ![58465, 648966, 3793767, 12149504, 241, 32, 1057, 1088, 1942, 2032, 8388704, 12860069,
    1252, 1334, 1500, 1131, 1115367, 6260357, 2651759, 4322539, 3187834, 1090714, 3083, 96]
    ![1, 8388610, 8388612, 8, 16, 32, 64, 128, 256, 512, 1024, 27654, 4096, 8397824, 8406016,
    32768, 66368, 131776, 262448, 525088, 1048784, 2097328, 12582918, 8388608] he hxi hf (by
    decide +kernel)
  have hc3 : monsterCo1GeometryVectorPoint94AfterInverseMatrix *
    monsterCo1GeometryVectorPoint46Matrix = monsterCo1GeometryVectorPoint94Matrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![1, 8388610, 8388612, 8, 16, 32, 64, 128, 256, 512, 1024, 27654, 4096, 8397824, 8406016,
    32768, 66368, 131776, 262448, 525088, 1048784, 2097328, 12582918, 8388608]
    ![4129584, 11155152, 9769516, 9773612, 12572128, 12575904, 12575824, 12572368, 12646839,
    12598907, 12518640, 8372028, 12830260, 209523, 11785966, 11592797, 9481184, 1153996,
    10656464, 2141068, 3979251, 12349491, 12842619, 50176]
    ![4129584, 11203280, 9819692, 9773612, 12572128, 12575904, 12575824, 12572368, 12646839,
    12598907, 12518640, 5209005, 12830260, 12382851, 792094, 11592797, 3115132, 13735735,
    6443559, 10455264, 8605843, 235427, 16520839, 50176] hf hy hc (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_line_products
    monsterCo1GeometryVectorPoint30Transport monsterCo1GeometryVectorPoint46Transport 2
    monsterCo1GeometryVectorPoint30Matrix monsterCo1GeometryVectorPoint30InverseMatrix
    monsterCo1GeometryVectorPoint46Matrix
    monsterCo1GeometryVectorPoint94AfterSignMatrix
    monsterCo1GeometryVectorPoint94AfterInverseMatrix monsterCo1GeometryVectorPoint94Matrix
    monsterCo1GeometryVectorPoint30Transport_binary
    monsterCo1GeometryVectorPoint30Transport_inverse_binary
    monsterCo1GeometryVectorPoint46Transport_binary
    hc1 hc2 hc3 v

/-- Source point 94 is the literal actual transported frame point. -/
def monsterCo1GeometryVectorPoint94 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryVectorPoint94Transport • monsterCo1GeometryBasePoint

/-- Complete binary coordinates of this literal actual source point. -/
theorem monsterCo1GeometryVectorPoint94_binary :
    monsterCo1GeometryVectorPoint94.val =
      ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0] := by
  change co1BinaryAction monsterCo1GeometryVectorPoint94Transport monsterCo1GeometryBasePoint.val =
      _
  rw [monsterCo1GeometryVectorPoint94Transport_binary, monsterCo1GeometryBasePoint_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
