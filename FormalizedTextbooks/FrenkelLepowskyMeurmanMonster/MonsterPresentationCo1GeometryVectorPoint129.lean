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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint068
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint082

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The literal actual two-core word for source point 129. -/
def monsterCo1GeometryVectorPoint129Transport : Co1 :=
  monsterCo1GeometryVectorPoint68Transport * monsterCo1GeometryTransportOperator 5 *
    monsterCo1GeometryVectorPoint68Transport⁻¹ * monsterCo1GeometryVectorPoint82Transport

/-- Complete displayed binary matrix of actual transport 129. -/
def monsterCo1GeometryVectorPoint129Matrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![1089, 2811410, 664852, 9052408, 58496, 64, 8445984, 8388672, 9968, 1280, 8389632,
      2164381, 2806046, 8389469, 10512187, 10511367, 11044364, 7614174, 11043320, 15841955,
      8389243, 9453916, 15896879, 8388688]

/-- First complete finite matrix product in literal actual transport 129. -/
def monsterCo1GeometryVectorPoint129AfterSignMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![58369, 8319649, 14587082, 7271025, 58416, 58465, 241, 57489, 1105926, 1756, 8388768,
      7426887, 14372964, 3188166, 9495565, 2138443, 12160694, 12782440, 11992974, 8356130,
      50428, 11534428, 13539866, 1233]

/-- Second complete finite matrix product in literal actual transport 129. -/
def monsterCo1GeometryVectorPoint129AfterInverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![57488, 774682, 1815312, 9139818, 58609, 57521, 1072, 58465, 8405403, 1648, 1024, 1085261,
      10158878, 1091405, 8388763, 9480007, 3636069, 3116816, 11111578, 1250884, 9454139,
      10543547, 15567082, 8389744]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 24000000 in
-- Check every entry of this finite actual transport matrix in the Lean kernel.
/-- Every column of transport 129 is its actual Conway binary action. -/
theorem monsterCo1GeometryVectorPoint129Transport_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint129Transport v =
      monsterCo1GeometryVectorPoint129Matrix *ᵥ v := by
  have hx : monsterCo1GeometryVectorPoint68Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![8447009, 8319970, 14587395, 15659966, 58384, 8447041, 8388849, 57521, 9494698, 8390364,
    8388768, 7426753, 14373409, 3187776, 1107105, 2138177, 12095129, 12716904, 12058052,
    16745217, 8439420, 3145754, 5216336, 8389841] := by decide +kernel
  have hxi : monsterCo1GeometryVectorPoint68InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![8447041, 1814606, 10203461, 1832414, 8389825, 58593, 58560, 58513, 9462487, 8430298,
    8447137, 7789041, 9328797, 1106432, 2130240, 3179312, 2985744, 6074661, 10890602, 16558164,
    41184, 10543537, 2316630, 1136] := by decide +kernel
  have hy : monsterCo1GeometryVectorPoint82Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![58529, 11003705, 10969406, 491731, 1152, 57504, 8446144, 8446016, 26608, 1504, 8389632,
    8496796, 8860884, 2138972, 10495547, 26086, 12925741, 1340223, 6830355, 8175491, 18043,
    11551158, 3287332, 8388784] := by rfl
  have he : monsterCo1GeometryVectorPoint129AfterSignMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![58369, 8319649, 14587082, 7271025, 58416, 58465, 241, 57489, 1105926, 1756, 8388768,
    7426887, 14372964, 3188166, 9495565, 2138443, 12160694, 12782440, 11992974, 8356130, 50428,
    11534428, 13539866, 1233] := by rfl
  have hf : monsterCo1GeometryVectorPoint129AfterInverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![57488, 774682, 1815312, 9139818, 58609, 57521, 1072, 58465, 8405403, 1648, 1024, 1085261,
    10158878, 1091405, 8388763, 9480007, 3636069, 3116816, 11111578, 1250884, 9454139,
    10543547, 15567082, 8389744] := by rfl
  have hc : monsterCo1GeometryVectorPoint129Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![1089, 2811410, 664852, 9052408, 58496, 64, 8445984, 8388672, 9968, 1280, 8389632,
    2164381, 2806046, 8389469, 10512187, 10511367, 11044364, 7614174, 11043320, 15841955,
    8389243, 9453916, 15896879, 8388688] := by rfl
  have hc1 : monsterCo1GeometryVectorPoint68Matrix *
    monsterCo1GeometryTransportOperatorMatrix 5 =
    monsterCo1GeometryVectorPoint129AfterSignMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![8447009, 8319970, 14587395, 15659966, 58384, 8447041, 8388849, 57521, 9494698, 8390364,
    8388768, 7426753, 14373409, 3187776, 1107105, 2138177, 12095129, 12716904, 12058052,
    16745217, 8439420, 3145754, 5216336, 8389841]
      (monsterCo1GeometryBinaryOperatorMasks 5)
    ![58369, 8319649, 14587082, 7271025, 58416, 58465, 241, 57489, 1105926, 1756, 8388768,
    7426887, 14372964, 3188166, 9495565, 2138443, 12160694, 12782440, 11992974, 8356130, 50428,
    11534428, 13539866, 1233] hx (monsterCo1GeometryBinaryOperatorMasks_decode 5) he
      (by decide +kernel)
  have hc2 : monsterCo1GeometryVectorPoint129AfterSignMatrix *
    monsterCo1GeometryVectorPoint68InverseMatrix =
    monsterCo1GeometryVectorPoint129AfterInverseMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![58369, 8319649, 14587082, 7271025, 58416, 58465, 241, 57489, 1105926, 1756, 8388768,
    7426887, 14372964, 3188166, 9495565, 2138443, 12160694, 12782440, 11992974, 8356130, 50428,
    11534428, 13539866, 1233]
    ![8447041, 1814606, 10203461, 1832414, 8389825, 58593, 58560, 58513, 9462487, 8430298,
    8447137, 7789041, 9328797, 1106432, 2130240, 3179312, 2985744, 6074661, 10890602, 16558164,
    41184, 10543537, 2316630, 1136]
    ![57488, 774682, 1815312, 9139818, 58609, 57521, 1072, 58465, 8405403, 1648, 1024, 1085261,
    10158878, 1091405, 8388763, 9480007, 3636069, 3116816, 11111578, 1250884, 9454139,
    10543547, 15567082, 8389744] he hxi hf (by decide +kernel)
  have hc3 : monsterCo1GeometryVectorPoint129AfterInverseMatrix *
    monsterCo1GeometryVectorPoint82Matrix = monsterCo1GeometryVectorPoint129Matrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![57488, 774682, 1815312, 9139818, 58609, 57521, 1072, 58465, 8405403, 1648, 1024, 1085261,
    10158878, 1091405, 8388763, 9480007, 3636069, 3116816, 11111578, 1250884, 9454139,
    10543547, 15567082, 8389744]
    ![58529, 11003705, 10969406, 491731, 1152, 57504, 8446144, 8446016, 26608, 1504, 8389632,
    8496796, 8860884, 2138972, 10495547, 26086, 12925741, 1340223, 6830355, 8175491, 18043,
    11551158, 3287332, 8388784]
    ![1089, 2811410, 664852, 9052408, 58496, 64, 8445984, 8388672, 9968, 1280, 8389632,
    2164381, 2806046, 8389469, 10512187, 10511367, 11044364, 7614174, 11043320, 15841955,
    8389243, 9453916, 15896879, 8388688] hf hy hc (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_line_products
    monsterCo1GeometryVectorPoint68Transport monsterCo1GeometryVectorPoint82Transport 5
    monsterCo1GeometryVectorPoint68Matrix monsterCo1GeometryVectorPoint68InverseMatrix
    monsterCo1GeometryVectorPoint82Matrix
    monsterCo1GeometryVectorPoint129AfterSignMatrix
    monsterCo1GeometryVectorPoint129AfterInverseMatrix monsterCo1GeometryVectorPoint129Matrix
    monsterCo1GeometryVectorPoint68Transport_binary
    monsterCo1GeometryVectorPoint68Transport_inverse_binary
    monsterCo1GeometryVectorPoint82Transport_binary
    hc1 hc2 hc3 v

/-- Source point 129 is the literal actual transported frame point. -/
def monsterCo1GeometryVectorPoint129 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryVectorPoint129Transport • monsterCo1GeometryBasePoint

/-- Complete binary coordinates of this literal actual source point. -/
theorem monsterCo1GeometryVectorPoint129_binary :
    monsterCo1GeometryVectorPoint129.val =
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0] := by
  change co1BinaryAction monsterCo1GeometryVectorPoint129Transport monsterCo1GeometryBasePoint.val =
      _
  rw [monsterCo1GeometryVectorPoint129Transport_binary, monsterCo1GeometryBasePoint_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
