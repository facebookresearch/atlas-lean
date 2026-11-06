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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint010
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint036

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The literal actual two-core word for source point 79. -/
def monsterCo1GeometryVectorPoint79Transport : Co1 :=
  monsterCo1GeometryVectorPoint10Transport * monsterCo1GeometryTransportOperator 1 *
    monsterCo1GeometryVectorPoint10Transport⁻¹ * monsterCo1GeometryVectorPoint36Transport

/-- Complete displayed binary matrix of actual transport 79. -/
def monsterCo1GeometryVectorPoint79Matrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![8446993, 12613647, 15785214, 14728430, 8445968, 8389680, 8446144, 8446016, 8421584,
      8405104, 58368, 1429165, 54928, 8423072, 8446288, 8422208, 1249866, 12770536, 15219988,
      6078025, 10495786, 1639, 12767334, 8445952]

/-- First complete finite matrix product in literal actual transport 79. -/
def monsterCo1GeometryVectorPoint79AfterSignMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![8388769, 4250767, 7404686, 6356110, 58384, 8389680, 58560, 58432, 34000, 17520, 8389632,
      14117611, 5245471, 9470465, 2146800, 3187680, 1290314, 12758248, 15231060, 14470281,
      10535514, 8390327, 343171, 8445952]

/-- Second complete finite matrix product in literal actual transport 79. -/
def monsterCo1GeometryVectorPoint79AfterInverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![8447200, 53856, 45904, 29200, 1040, 32, 1088, 1152, 1280, 1536, 1024, 7950, 814, 8389037,
      8388763, 8389079, 116076, 144019, 292376, 529198, 9453723, 10544353, 16587344, 8389632]

set_option maxHeartbeats 24000000 in
-- Check every entry of this finite actual transport matrix in the Lean kernel.
/-- Every column of transport 79 is its actual Conway binary action. -/
theorem monsterCo1GeometryVectorPoint79Transport_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint79Transport v =
      monsterCo1GeometryVectorPoint79Matrix *ᵥ v := by
  have hx : monsterCo1GeometryVectorPoint10Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![161, 12635279, 15788942, 14739854, 8445968, 8389680, 8446144, 8446016, 8421584, 8405104,
    8389632, 5732571, 13637663, 9470977, 2146544, 3186912, 1290874, 12762360, 15235412,
    6086281, 10535770, 1719, 338093, 58368] := by decide +kernel
  have hxi : monsterCo1GeometryVectorPoint10InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![8388849, 9292920, 11397572, 1960382, 8389648, 8388656, 8389760, 192, 8405147, 49484,
    8446177, 8380771, 8402563, 8446737, 58945, 8447409, 11731829, 2233916, 12321148, 9762476,
    49472, 17296, 4336290, 8447201] := by decide +kernel
  have hy : monsterCo1GeometryVectorPoint36Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![8446976, 8392704, 4864, 4352, 8389648, 8389680, 8389824, 8389696, 8414416, 8430704,
    58368, 12919938, 5299343, 9437345, 2146464, 3195040, 8622186, 8540390, 554234, 832598,
    1754, 1654, 13686945, 8389632] := by decide +kernel
  have he : monsterCo1GeometryVectorPoint79AfterSignMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![8388769, 4250767, 7404686, 6356110, 58384, 8389680, 58560, 58432, 34000, 17520, 8389632,
    14117611, 5245471, 9470465, 2146800, 3187680, 1290314, 12758248, 15231060, 14470281,
    10535514, 8390327, 343171, 8445952] := by rfl
  have hf : monsterCo1GeometryVectorPoint79AfterInverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![8447200, 53856, 45904, 29200, 1040, 32, 1088, 1152, 1280, 1536, 1024, 7950, 814, 8389037,
    8388763, 8389079, 116076, 144019, 292376, 529198, 9453723, 10544353, 16587344, 8389632] :=
    by decide +kernel
  have hc : monsterCo1GeometryVectorPoint79Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![8446993, 12613647, 15785214, 14728430, 8445968, 8389680, 8446144, 8446016, 8421584,
    8405104, 58368, 1429165, 54928, 8423072, 8446288, 8422208, 1249866, 12770536, 15219988,
    6078025, 10495786, 1639, 12767334, 8445952] := by rfl
  have hc1 : monsterCo1GeometryVectorPoint10Matrix *
    monsterCo1GeometryTransportOperatorMatrix 1 =
    monsterCo1GeometryVectorPoint79AfterSignMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![161, 12635279, 15788942, 14739854, 8445968, 8389680, 8446144, 8446016, 8421584, 8405104,
    8389632, 5732571, 13637663, 9470977, 2146544, 3186912, 1290874, 12762360, 15235412,
    6086281, 10535770, 1719, 338093, 58368]
      (monsterCo1GeometryBinaryOperatorMasks 1)
    ![8388769, 4250767, 7404686, 6356110, 58384, 8389680, 58560, 58432, 34000, 17520, 8389632,
    14117611, 5245471, 9470465, 2146800, 3187680, 1290314, 12758248, 15231060, 14470281,
    10535514, 8390327, 343171, 8445952] hx (monsterCo1GeometryBinaryOperatorMasks_decode 1) he
    (by decide +kernel)
  have hc2 : monsterCo1GeometryVectorPoint79AfterSignMatrix *
    monsterCo1GeometryVectorPoint10InverseMatrix =
    monsterCo1GeometryVectorPoint79AfterInverseMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![8388769, 4250767, 7404686, 6356110, 58384, 8389680, 58560, 58432, 34000, 17520, 8389632,
    14117611, 5245471, 9470465, 2146800, 3187680, 1290314, 12758248, 15231060, 14470281,
    10535514, 8390327, 343171, 8445952]
    ![8388849, 9292920, 11397572, 1960382, 8389648, 8388656, 8389760, 192, 8405147, 49484,
    8446177, 8380771, 8402563, 8446737, 58945, 8447409, 11731829, 2233916, 12321148, 9762476,
    49472, 17296, 4336290, 8447201]
    ![8447200, 53856, 45904, 29200, 1040, 32, 1088, 1152, 1280, 1536, 1024, 7950, 814, 8389037,
    8388763, 8389079, 116076, 144019, 292376, 529198, 9453723, 10544353, 16587344, 8389632] he
    hxi hf (by decide +kernel)
  have hc3 : monsterCo1GeometryVectorPoint79AfterInverseMatrix *
    monsterCo1GeometryVectorPoint36Matrix = monsterCo1GeometryVectorPoint79Matrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![8447200, 53856, 45904, 29200, 1040, 32, 1088, 1152, 1280, 1536, 1024, 7950, 814, 8389037,
    8388763, 8389079, 116076, 144019, 292376, 529198, 9453723, 10544353, 16587344, 8389632]
    ![8446976, 8392704, 4864, 4352, 8389648, 8389680, 8389824, 8389696, 8414416, 8430704,
    58368, 12919938, 5299343, 9437345, 2146464, 3195040, 8622186, 8540390, 554234, 832598,
    1754, 1654, 13686945, 8389632]
    ![8446993, 12613647, 15785214, 14728430, 8445968, 8389680, 8446144, 8446016, 8421584,
    8405104, 58368, 1429165, 54928, 8423072, 8446288, 8422208, 1249866, 12770536, 15219988,
    6078025, 10495786, 1639, 12767334, 8445952] hf hy hc (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_line_products
    monsterCo1GeometryVectorPoint10Transport monsterCo1GeometryVectorPoint36Transport 1
    monsterCo1GeometryVectorPoint10Matrix monsterCo1GeometryVectorPoint10InverseMatrix
    monsterCo1GeometryVectorPoint36Matrix
    monsterCo1GeometryVectorPoint79AfterSignMatrix
    monsterCo1GeometryVectorPoint79AfterInverseMatrix monsterCo1GeometryVectorPoint79Matrix
    monsterCo1GeometryVectorPoint10Transport_binary
    monsterCo1GeometryVectorPoint10Transport_inverse_binary
    monsterCo1GeometryVectorPoint36Transport_binary
    hc1 hc2 hc3 v

/-- Source point 79 is the literal actual transported frame point. -/
def monsterCo1GeometryVectorPoint79 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryVectorPoint79Transport • monsterCo1GeometryBasePoint

/-- Complete binary coordinates of this literal actual source point. -/
theorem monsterCo1GeometryVectorPoint79_binary :
    monsterCo1GeometryVectorPoint79.val =
      ![0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0] := by
  change co1BinaryAction monsterCo1GeometryVectorPoint79Transport monsterCo1GeometryBasePoint.val =
      _
  rw [monsterCo1GeometryVectorPoint79Transport_binary, monsterCo1GeometryBasePoint_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
