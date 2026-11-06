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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint009
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint036

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The literal actual two-core word for source point 78. -/
def monsterCo1GeometryVectorPoint78Transport : Co1 :=
  monsterCo1GeometryVectorPoint9Transport * monsterCo1GeometryTransportOperator 1 *
    monsterCo1GeometryVectorPoint9Transport⁻¹ * monsterCo1GeometryVectorPoint36Transport

/-- Complete displayed binary matrix of actual transport 78. -/
def monsterCo1GeometryVectorPoint78Matrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![8447025, 12630031, 15760494, 14736478, 8389648, 8446000, 8446144, 8446016, 8421584,
      8405104, 58368, 1429165, 54960, 8406688, 8405440, 8446960, 12835940, 1184454, 5799621,
      16531256, 1771, 11543846, 12833002, 8445952]

/-- First complete finite matrix product in literal actual transport 78. -/
def monsterCo1GeometryVectorPoint78AfterSignMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![8388769, 4250767, 7404686, 6356110, 8389648, 58416, 58560, 58432, 34000, 17520, 8389632,
      14068327, 5245503, 9454081, 2122080, 3195728, 12807268, 1208518, 14208133, 16558328,
      8390299, 11584246, 343171, 8445952]

/-- Second complete finite matrix product in literal actual transport 78. -/
def monsterCo1GeometryVectorPoint78AfterInverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![8447184, 53648, 45344, 29600, 16, 1056, 1088, 1152, 1280, 1536, 1024, 7950, 798, 8389213,
      8389355, 8388711, 78179, 181916, 267038, 570660, 9495761, 10518631, 16652704, 8389632]

set_option maxHeartbeats 24000000 in
-- Check every entry of this finite actual transport matrix in the Lean kernel.
/-- Every column of transport 78 is its actual Conway binary action. -/
theorem monsterCo1GeometryVectorPoint78Transport_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint78Transport v =
      monsterCo1GeometryVectorPoint78Matrix *ᵥ v := by
  have hx : monsterCo1GeometryVectorPoint9Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![161, 12635279, 15788942, 14739854, 8389648, 8446000, 8446144, 8446016, 8421584, 8405104,
    8389632, 5683319, 13637695, 9454593, 2121824, 3194960, 12811348, 1209046, 5824133,
    16563192, 1691, 11583990, 338093, 58368] := by decide +kernel
  have hxi : monsterCo1GeometryVectorPoint9InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![8388849, 9358516, 3074686, 10414792, 1040, 8388656, 8389760, 192, 8405739, 49804,
    8446161, 8381075, 8402243, 8446753, 8447601, 58753, 11731897, 10622597, 12321468, 1374176,
    49792, 16864, 4270418, 8447185] := by decide +kernel
  have hy : monsterCo1GeometryVectorPoint36Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![8446976, 8392704, 4864, 4352, 8389648, 8389680, 8389824, 8389696, 8414416, 8430704,
    58368, 12919938, 5299343, 9437345, 2146464, 3195040, 8622186, 8540390, 554234, 832598,
    1754, 1654, 13686945, 8389632] := by decide +kernel
  have he : monsterCo1GeometryVectorPoint78AfterSignMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![8388769, 4250767, 7404686, 6356110, 8389648, 58416, 58560, 58432, 34000, 17520, 8389632,
    14068327, 5245503, 9454081, 2122080, 3195728, 12807268, 1208518, 14208133, 16558328,
    8390299, 11584246, 343171, 8445952] := by rfl
  have hf : monsterCo1GeometryVectorPoint78AfterInverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![8447184, 53648, 45344, 29600, 16, 1056, 1088, 1152, 1280, 1536, 1024, 7950, 798, 8389213,
    8389355, 8388711, 78179, 181916, 267038, 570660, 9495761, 10518631, 16652704, 8389632] :=
    by decide +kernel
  have hc : monsterCo1GeometryVectorPoint78Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![8447025, 12630031, 15760494, 14736478, 8389648, 8446000, 8446144, 8446016, 8421584,
    8405104, 58368, 1429165, 54960, 8406688, 8405440, 8446960, 12835940, 1184454, 5799621,
    16531256, 1771, 11543846, 12833002, 8445952] := by rfl
  have hc1 : monsterCo1GeometryVectorPoint9Matrix * monsterCo1GeometryTransportOperatorMatrix
    1 = monsterCo1GeometryVectorPoint78AfterSignMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![161, 12635279, 15788942, 14739854, 8389648, 8446000, 8446144, 8446016, 8421584, 8405104,
    8389632, 5683319, 13637695, 9454593, 2121824, 3194960, 12811348, 1209046, 5824133,
    16563192, 1691, 11583990, 338093, 58368]
      (monsterCo1GeometryBinaryOperatorMasks 1)
    ![8388769, 4250767, 7404686, 6356110, 8389648, 58416, 58560, 58432, 34000, 17520, 8389632,
    14068327, 5245503, 9454081, 2122080, 3195728, 12807268, 1208518, 14208133, 16558328,
    8390299, 11584246, 343171, 8445952] hx (monsterCo1GeometryBinaryOperatorMasks_decode 1) he
    (by decide +kernel)
  have hc2 : monsterCo1GeometryVectorPoint78AfterSignMatrix *
    monsterCo1GeometryVectorPoint9InverseMatrix =
    monsterCo1GeometryVectorPoint78AfterInverseMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![8388769, 4250767, 7404686, 6356110, 8389648, 58416, 58560, 58432, 34000, 17520, 8389632,
    14068327, 5245503, 9454081, 2122080, 3195728, 12807268, 1208518, 14208133, 16558328,
    8390299, 11584246, 343171, 8445952]
    ![8388849, 9358516, 3074686, 10414792, 1040, 8388656, 8389760, 192, 8405739, 49804,
    8446161, 8381075, 8402243, 8446753, 8447601, 58753, 11731897, 10622597, 12321468, 1374176,
    49792, 16864, 4270418, 8447185]
    ![8447184, 53648, 45344, 29600, 16, 1056, 1088, 1152, 1280, 1536, 1024, 7950, 798, 8389213,
    8389355, 8388711, 78179, 181916, 267038, 570660, 9495761, 10518631, 16652704, 8389632] he
    hxi hf (by decide +kernel)
  have hc3 : monsterCo1GeometryVectorPoint78AfterInverseMatrix *
    monsterCo1GeometryVectorPoint36Matrix = monsterCo1GeometryVectorPoint78Matrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![8447184, 53648, 45344, 29600, 16, 1056, 1088, 1152, 1280, 1536, 1024, 7950, 798, 8389213,
    8389355, 8388711, 78179, 181916, 267038, 570660, 9495761, 10518631, 16652704, 8389632]
    ![8446976, 8392704, 4864, 4352, 8389648, 8389680, 8389824, 8389696, 8414416, 8430704,
    58368, 12919938, 5299343, 9437345, 2146464, 3195040, 8622186, 8540390, 554234, 832598,
    1754, 1654, 13686945, 8389632]
    ![8447025, 12630031, 15760494, 14736478, 8389648, 8446000, 8446144, 8446016, 8421584,
    8405104, 58368, 1429165, 54960, 8406688, 8405440, 8446960, 12835940, 1184454, 5799621,
    16531256, 1771, 11543846, 12833002, 8445952] hf hy hc (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_line_products
    monsterCo1GeometryVectorPoint9Transport monsterCo1GeometryVectorPoint36Transport 1
    monsterCo1GeometryVectorPoint9Matrix monsterCo1GeometryVectorPoint9InverseMatrix
    monsterCo1GeometryVectorPoint36Matrix
    monsterCo1GeometryVectorPoint78AfterSignMatrix
    monsterCo1GeometryVectorPoint78AfterInverseMatrix monsterCo1GeometryVectorPoint78Matrix
    monsterCo1GeometryVectorPoint9Transport_binary
    monsterCo1GeometryVectorPoint9Transport_inverse_binary
    monsterCo1GeometryVectorPoint36Transport_binary
    hc1 hc2 hc3 v

/-- Source point 78 is the literal actual transported frame point. -/
def monsterCo1GeometryVectorPoint78 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryVectorPoint78Transport • monsterCo1GeometryBasePoint

/-- Complete binary coordinates of this literal actual source point. -/
theorem monsterCo1GeometryVectorPoint78_binary :
    monsterCo1GeometryVectorPoint78.val =
      ![0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0] := by
  change co1BinaryAction monsterCo1GeometryVectorPoint78Transport monsterCo1GeometryBasePoint.val =
      _
  rw [monsterCo1GeometryVectorPoint78Transport_binary, monsterCo1GeometryBasePoint_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
