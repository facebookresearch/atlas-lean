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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint026
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint043

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The literal actual two-core word for source point 92. -/
def monsterCo1GeometryVectorPoint92Transport : Co1 :=
  monsterCo1GeometryVectorPoint26Transport * monsterCo1GeometryTransportOperator 3 *
    monsterCo1GeometryVectorPoint26Transport⁻¹ * monsterCo1GeometryVectorPoint43Transport

/-- Complete displayed binary matrix of actual transport 92. -/
def monsterCo1GeometryVectorPoint92Matrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![4129008, 2752592, 5572775, 5572779, 5392, 12608, 53792, 12928, 53248, 12288, 8437760,
      5517996, 13376, 13504, 34272, 18272, 78336, 1168044, 131340, 7813623, 209487, 7596137,
      2048, 50176]

/-- First complete finite matrix product in literal actual transport 92. -/
def monsterCo1GeometryVectorPoint92AfterSignMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![768, 256, 33280, 16896, 53520, 12608, 53792, 12928, 53248, 12288, 50176, 2048, 2802012,
      4178940, 4212747, 4229127, 78336, 315904, 143616, 577792, 196803, 786482, 4196352,
      8389632]

/-- Second complete finite matrix product in literal actual transport 92. -/
def monsterCo1GeometryVectorPoint92AfterInverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![1, 2, 8388612, 8, 16, 32, 64, 128, 256, 512, 8389632, 4212736, 5134, 9229, 16395, 33799,
      66016, 131984, 263056, 524912, 1049200, 2097632, 4194315, 8388608]

set_option maxHeartbeats 24000000 in
-- Check every entry of this finite actual transport matrix in the Lean kernel.
/-- Every column of transport 92 is its actual Conway binary action. -/
theorem monsterCo1GeometryVectorPoint92Transport_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint92Transport v =
      monsterCo1GeometryVectorPoint92Matrix *ᵥ v := by
  have hx : monsterCo1GeometryVectorPoint26Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![768, 256, 8422912, 16896, 53520, 12608, 53792, 12928, 53248, 12288, 8437760, 18443,
    2802780, 4179196, 4196363, 4246535, 78816, 315792, 144016, 578416, 197299, 786898, 4212736,
    8389632] := by decide +kernel
  have hxi : monsterCo1GeometryVectorPoint26InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![4129008, 2752592, 13993131, 5587115, 274, 323, 546, 643, 2, 3, 1036, 4212736, 8388876,
    8389388, 11, 8388615, 66531, 262546, 131731, 525170, 209584, 840144, 18443, 8389644] := by
      decide +kernel
  have hy : monsterCo1GeometryVectorPoint43Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![4129008, 2752592, 5622951, 5572779, 5392, 12608, 53792, 12928, 53248, 12288, 8389632,
    5553996, 11203612, 12579900, 4230635, 12619623, 78816, 1119548, 181916, 7864199, 259135,
    7596425, 4194315, 50176] := by decide +kernel
  have he : monsterCo1GeometryVectorPoint92AfterSignMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![768, 256, 33280, 16896, 53520, 12608, 53792, 12928, 53248, 12288, 50176, 2048, 2802012,
    4178940, 4212747, 4229127, 78336, 315904, 143616, 577792, 196803, 786482, 4196352, 8389632]
    := by rfl
  have hf : monsterCo1GeometryVectorPoint92AfterInverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![1, 2, 8388612, 8, 16, 32, 64, 128, 256, 512, 8389632, 4212736, 5134, 9229, 16395, 33799,
    66016, 131984, 263056, 524912, 1049200, 2097632, 4194315, 8388608] := by rfl
  have hc : monsterCo1GeometryVectorPoint92Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![4129008, 2752592, 5572775, 5572779, 5392, 12608, 53792, 12928, 53248, 12288, 8437760,
    5517996, 13376, 13504, 34272, 18272, 78336, 1168044, 131340, 7813623, 209487, 7596137,
    2048, 50176] := by rfl
  have hc1 : monsterCo1GeometryVectorPoint26Matrix *
    monsterCo1GeometryTransportOperatorMatrix 3 =
    monsterCo1GeometryVectorPoint92AfterSignMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![768, 256, 8422912, 16896, 53520, 12608, 53792, 12928, 53248, 12288, 8437760, 18443,
    2802780, 4179196, 4196363, 4246535, 78816, 315792, 144016, 578416, 197299, 786898, 4212736,
    8389632]
      (monsterCo1GeometryBinaryOperatorMasks 3)
    ![768, 256, 33280, 16896, 53520, 12608, 53792, 12928, 53248, 12288, 50176, 2048, 2802012,
    4178940, 4212747, 4229127, 78336, 315904, 143616, 577792, 196803, 786482, 4196352, 8389632]
    hx (monsterCo1GeometryBinaryOperatorMasks_decode 3) he (by decide +kernel)
  have hc2 : monsterCo1GeometryVectorPoint92AfterSignMatrix *
    monsterCo1GeometryVectorPoint26InverseMatrix =
    monsterCo1GeometryVectorPoint92AfterInverseMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![768, 256, 33280, 16896, 53520, 12608, 53792, 12928, 53248, 12288, 50176, 2048, 2802012,
    4178940, 4212747, 4229127, 78336, 315904, 143616, 577792, 196803, 786482, 4196352, 8389632]
    ![4129008, 2752592, 13993131, 5587115, 274, 323, 546, 643, 2, 3, 1036, 4212736, 8388876,
    8389388, 11, 8388615, 66531, 262546, 131731, 525170, 209584, 840144, 18443, 8389644]
    ![1, 2, 8388612, 8, 16, 32, 64, 128, 256, 512, 8389632, 4212736, 5134, 9229, 16395, 33799,
    66016, 131984, 263056, 524912, 1049200, 2097632, 4194315, 8388608] he hxi hf
      (by decide +kernel)
  have hc3 : monsterCo1GeometryVectorPoint92AfterInverseMatrix *
    monsterCo1GeometryVectorPoint43Matrix = monsterCo1GeometryVectorPoint92Matrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![1, 2, 8388612, 8, 16, 32, 64, 128, 256, 512, 8389632, 4212736, 5134, 9229, 16395, 33799,
    66016, 131984, 263056, 524912, 1049200, 2097632, 4194315, 8388608]
    ![4129008, 2752592, 5622951, 5572779, 5392, 12608, 53792, 12928, 53248, 12288, 8389632,
    5553996, 11203612, 12579900, 4230635, 12619623, 78816, 1119548, 181916, 7864199, 259135,
    7596425, 4194315, 50176]
    ![4129008, 2752592, 5572775, 5572779, 5392, 12608, 53792, 12928, 53248, 12288, 8437760,
    5517996, 13376, 13504, 34272, 18272, 78336, 1168044, 131340, 7813623, 209487, 7596137,
    2048, 50176] hf hy hc (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_line_products
    monsterCo1GeometryVectorPoint26Transport monsterCo1GeometryVectorPoint43Transport 3
    monsterCo1GeometryVectorPoint26Matrix monsterCo1GeometryVectorPoint26InverseMatrix
    monsterCo1GeometryVectorPoint43Matrix
    monsterCo1GeometryVectorPoint92AfterSignMatrix
    monsterCo1GeometryVectorPoint92AfterInverseMatrix monsterCo1GeometryVectorPoint92Matrix
    monsterCo1GeometryVectorPoint26Transport_binary
    monsterCo1GeometryVectorPoint26Transport_inverse_binary
    monsterCo1GeometryVectorPoint43Transport_binary
    hc1 hc2 hc3 v

/-- Source point 92 is the literal actual transported frame point. -/
def monsterCo1GeometryVectorPoint92 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryVectorPoint92Transport • monsterCo1GeometryBasePoint

/-- Complete binary coordinates of this literal actual source point. -/
theorem monsterCo1GeometryVectorPoint92_binary :
    monsterCo1GeometryVectorPoint92.val =
      ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0] := by
  change co1BinaryAction monsterCo1GeometryVectorPoint92Transport monsterCo1GeometryBasePoint.val =
      _
  rw [monsterCo1GeometryVectorPoint92Transport_binary, monsterCo1GeometryBasePoint_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
