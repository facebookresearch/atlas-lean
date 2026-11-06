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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint039
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint078

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The literal actual two-core word for source point 125. -/
def monsterCo1GeometryVectorPoint125Transport : Co1 :=
  monsterCo1GeometryVectorPoint39Transport * monsterCo1GeometryTransportOperator 1 *
    monsterCo1GeometryVectorPoint39Transport⁻¹ * monsterCo1GeometryVectorPoint78Transport

/-- Complete displayed binary matrix of actual transport 125. -/
def monsterCo1GeometryVectorPoint125Matrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![8388640, 8401920, 22416, 38320, 8445968, 8446000, 8389824, 8389696, 8414416, 8430704,
      58368, 12919938, 5257391, 9446561, 2130992, 3163152, 5487172, 5405384, 12112683,
      11325735, 10535707, 11583799, 78339, 8389632]

/-- First complete finite matrix product in literal actual transport 125. -/
def monsterCo1GeometryVectorPoint125AfterSignMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![57505, 4250767, 7404686, 6356110, 58384, 8389680, 58560, 58432, 34000, 17520, 8389632,
      14138491, 5245471, 9463297, 2106864, 3164128, 9679994, 12732664, 15231060, 14470281,
      10520106, 8421991, 5627916, 8445952]

/-- Second complete finite matrix product in literal actual transport 125. -/
def monsterCo1GeometryVectorPoint125AfterInverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![8447200, 53856, 45904, 29200, 1040, 32, 1088, 1152, 1280, 1536, 1024, 7950, 814, 8389037,
      8388763, 8389079, 116076, 144019, 292376, 529198, 9453723, 10544353, 16587344, 8389632]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 24000000 in
-- Check every entry of this finite actual transport matrix in the Lean kernel.
/-- Every column of transport 125 is its actual Conway binary action. -/
theorem monsterCo1GeometryVectorPoint125Transport_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint125Transport v =
      monsterCo1GeometryVectorPoint125Matrix *ᵥ v := by
  have hx : monsterCo1GeometryVectorPoint39Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![58529, 12635279, 15788942, 14739854, 8445968, 8389680, 8446144, 8446016, 8421584,
    8405104, 8389632, 5746251, 13637663, 1074177, 10494192, 11550944, 9680458, 4349160,
    15235412, 6086281, 2130730, 8423015, 14018082, 58368] := by decide +kernel
  have hxi : monsterCo1GeometryVectorPoint39InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![241, 9296982, 3013866, 10354576, 8389648, 8388656, 8389760, 192, 8406171, 49484, 8447201,
    8382045, 8401539, 8447761, 57921, 8446385, 3342405, 2234156, 12321404, 1372332, 49472,
    8406928, 12730034, 8446177] := by decide +kernel
  have hy : monsterCo1GeometryVectorPoint78Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![8447025, 12630031, 15760494, 14736478, 8389648, 8446000, 8446144, 8446016, 8421584,
    8405104, 58368, 1429165, 54960, 8406688, 8405440, 8446960, 12835940, 1184454, 5799621,
    16531256, 1771, 11543846, 12833002, 8445952] := by rfl
  have he : monsterCo1GeometryVectorPoint125AfterSignMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![57505, 4250767, 7404686, 6356110, 58384, 8389680, 58560, 58432, 34000, 17520, 8389632,
    14138491, 5245471, 9463297, 2106864, 3164128, 9679994, 12732664, 15231060, 14470281,
    10520106, 8421991, 5627916, 8445952] := by rfl
  have hf : monsterCo1GeometryVectorPoint125AfterInverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![8447200, 53856, 45904, 29200, 1040, 32, 1088, 1152, 1280, 1536, 1024, 7950, 814, 8389037,
    8388763, 8389079, 116076, 144019, 292376, 529198, 9453723, 10544353, 16587344, 8389632] :=
    by decide +kernel
  have hc : monsterCo1GeometryVectorPoint125Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![8388640, 8401920, 22416, 38320, 8445968, 8446000, 8389824, 8389696, 8414416, 8430704,
    58368, 12919938, 5257391, 9446561, 2130992, 3163152, 5487172, 5405384, 12112683, 11325735,
    10535707, 11583799, 78339, 8389632] := by rfl
  have hc1 : monsterCo1GeometryVectorPoint39Matrix *
    monsterCo1GeometryTransportOperatorMatrix 1 =
    monsterCo1GeometryVectorPoint125AfterSignMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![58529, 12635279, 15788942, 14739854, 8445968, 8389680, 8446144, 8446016, 8421584,
    8405104, 8389632, 5746251, 13637663, 1074177, 10494192, 11550944, 9680458, 4349160,
    15235412, 6086281, 2130730, 8423015, 14018082, 58368]
      (monsterCo1GeometryBinaryOperatorMasks 1)
    ![57505, 4250767, 7404686, 6356110, 58384, 8389680, 58560, 58432, 34000, 17520, 8389632,
    14138491, 5245471, 9463297, 2106864, 3164128, 9679994, 12732664, 15231060, 14470281,
    10520106, 8421991, 5627916, 8445952] hx (monsterCo1GeometryBinaryOperatorMasks_decode 1) he
    (by decide +kernel)
  have hc2 : monsterCo1GeometryVectorPoint125AfterSignMatrix *
    monsterCo1GeometryVectorPoint39InverseMatrix =
    monsterCo1GeometryVectorPoint125AfterInverseMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![57505, 4250767, 7404686, 6356110, 58384, 8389680, 58560, 58432, 34000, 17520, 8389632,
    14138491, 5245471, 9463297, 2106864, 3164128, 9679994, 12732664, 15231060, 14470281,
    10520106, 8421991, 5627916, 8445952]
    ![241, 9296982, 3013866, 10354576, 8389648, 8388656, 8389760, 192, 8406171, 49484, 8447201,
    8382045, 8401539, 8447761, 57921, 8446385, 3342405, 2234156, 12321404, 1372332, 49472,
    8406928, 12730034, 8446177]
    ![8447200, 53856, 45904, 29200, 1040, 32, 1088, 1152, 1280, 1536, 1024, 7950, 814, 8389037,
    8388763, 8389079, 116076, 144019, 292376, 529198, 9453723, 10544353, 16587344, 8389632] he
    hxi hf (by decide +kernel)
  have hc3 : monsterCo1GeometryVectorPoint125AfterInverseMatrix *
    monsterCo1GeometryVectorPoint78Matrix = monsterCo1GeometryVectorPoint125Matrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![8447200, 53856, 45904, 29200, 1040, 32, 1088, 1152, 1280, 1536, 1024, 7950, 814, 8389037,
    8388763, 8389079, 116076, 144019, 292376, 529198, 9453723, 10544353, 16587344, 8389632]
    ![8447025, 12630031, 15760494, 14736478, 8389648, 8446000, 8446144, 8446016, 8421584,
    8405104, 58368, 1429165, 54960, 8406688, 8405440, 8446960, 12835940, 1184454, 5799621,
    16531256, 1771, 11543846, 12833002, 8445952]
    ![8388640, 8401920, 22416, 38320, 8445968, 8446000, 8389824, 8389696, 8414416, 8430704,
    58368, 12919938, 5257391, 9446561, 2130992, 3163152, 5487172, 5405384, 12112683, 11325735,
    10535707, 11583799, 78339, 8389632] hf hy hc (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_line_products
    monsterCo1GeometryVectorPoint39Transport monsterCo1GeometryVectorPoint78Transport 1
    monsterCo1GeometryVectorPoint39Matrix monsterCo1GeometryVectorPoint39InverseMatrix
    monsterCo1GeometryVectorPoint78Matrix
    monsterCo1GeometryVectorPoint125AfterSignMatrix
    monsterCo1GeometryVectorPoint125AfterInverseMatrix monsterCo1GeometryVectorPoint125Matrix
    monsterCo1GeometryVectorPoint39Transport_binary
    monsterCo1GeometryVectorPoint39Transport_inverse_binary
    monsterCo1GeometryVectorPoint78Transport_binary
    hc1 hc2 hc3 v

/-- Source point 125 is the literal actual transported frame point. -/
def monsterCo1GeometryVectorPoint125 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryVectorPoint125Transport • monsterCo1GeometryBasePoint

/-- Complete binary coordinates of this literal actual source point. -/
theorem monsterCo1GeometryVectorPoint125_binary :
    monsterCo1GeometryVectorPoint125.val =
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0] := by
  change co1BinaryAction monsterCo1GeometryVectorPoint125Transport monsterCo1GeometryBasePoint.val =
      _
  rw [monsterCo1GeometryVectorPoint125Transport_binary, monsterCo1GeometryBasePoint_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
