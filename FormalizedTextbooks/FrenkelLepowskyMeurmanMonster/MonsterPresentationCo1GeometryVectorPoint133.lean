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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint019
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint085

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The literal actual two-core word for source point 133. -/
def monsterCo1GeometryVectorPoint133Transport : Co1 :=
  monsterCo1GeometryVectorPoint19Transport * monsterCo1GeometryTransportOperator 6 *
    monsterCo1GeometryVectorPoint19Transport⁻¹ * monsterCo1GeometryVectorPoint85Transport

/-- Complete displayed binary matrix of actual transport 133. -/
def monsterCo1GeometryVectorPoint133Matrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![9412031, 8171670, 1023060, 573574, 15784159, 6847405, 1522412, 8389696, 15196598,
      8647046, 1614519, 14896709, 15120153, 9817637, 7840535, 6768412, 420914, 3343547,
      12352836, 3816029, 3172310, 7742129, 2419173, 10220945]

/-- First complete finite matrix product in literal actual transport 133. -/
def monsterCo1GeometryVectorPoint133AfterSignMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![4353777, 9470999, 4360784, 11585115, 12758848, 5400599, 13805943, 81, 1049110, 1089798,
      1099686, 15149499, 6267051, 1267803, 12892037, 9470630, 816298, 13626354, 4729105,
      9013027, 6317679, 14759292, 15165104, 8446992]

/-- Second complete finite matrix product in literal actual transport 133. -/
def monsterCo1GeometryVectorPoint133AfterInverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![12823778, 6443908, 4434500, 3429151, 11688111, 2193954, 5279262, 128, 6653827, 9675641,
      1341151, 2169949, 15830176, 5740224, 12968424, 15041508, 14975008, 2298973, 14702638,
      5847055, 3187212, 7793930, 13900323, 8869569]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 24000000 in
-- Check every entry of this finite actual transport matrix in the Lean kernel.
/-- Every column of transport 133 is its actual Conway binary action. -/
theorem monsterCo1GeometryVectorPoint133Transport_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint133Transport v =
      monsterCo1GeometryVectorPoint133Matrix *ᵥ v := by
  have hx : monsterCo1GeometryVectorPoint19Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![12610622, 1082881, 12617871, 11585425, 12627151, 5270046, 5286462, 81, 1049296, 1090112,
    9487904, 15018925, 14655972, 1137437, 4503327, 9470128, 816252, 13494756, 13248834,
    9012464, 14705891, 6370431, 6776633, 58368] := by decide +kernel
  have hxi : monsterCo1GeometryVectorPoint19InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![534, 10952565, 4365618, 6678701, 8390307, 1089, 8389685, 241, 7774219, 8423168, 8869733,
    12702185, 9037574, 480068, 8868407, 8869398, 2004638, 12851129, 3736561, 9552297, 8422503,
    16163846, 4308884, 8867938] := by decide +kernel
  have hy : monsterCo1GeometryVectorPoint85Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![58529, 1790917, 10162478, 759097, 8445968, 57424, 8446144, 8389696, 8390352, 42848,
    8389632, 144950, 9167138, 1050214, 9454365, 8430026, 8027952, 13794504, 11072359, 5021406,
    3170570, 33287, 3037368, 1136] := by rfl
  have he : monsterCo1GeometryVectorPoint133AfterSignMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![4353777, 9470999, 4360784, 11585115, 12758848, 5400599, 13805943, 81, 1049110, 1089798,
    1099686, 15149499, 6267051, 1267803, 12892037, 9470630, 816298, 13626354, 4729105, 9013027,
    6317679, 14759292, 15165104, 8446992] := by rfl
  have hf : monsterCo1GeometryVectorPoint133AfterInverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![12823778, 6443908, 4434500, 3429151, 11688111, 2193954, 5279262, 128, 6653827, 9675641,
    1341151, 2169949, 15830176, 5740224, 12968424, 15041508, 14975008, 2298973, 14702638,
    5847055, 3187212, 7793930, 13900323, 8869569] := by rfl
  have hc : monsterCo1GeometryVectorPoint133Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![9412031, 8171670, 1023060, 573574, 15784159, 6847405, 1522412, 8389696, 15196598,
    8647046, 1614519, 14896709, 15120153, 9817637, 7840535, 6768412, 420914, 3343547, 12352836,
    3816029, 3172310, 7742129, 2419173, 10220945] := by rfl
  have hc1 : monsterCo1GeometryVectorPoint19Matrix *
    monsterCo1GeometryTransportOperatorMatrix 6 =
    monsterCo1GeometryVectorPoint133AfterSignMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![12610622, 1082881, 12617871, 11585425, 12627151, 5270046, 5286462, 81, 1049296, 1090112,
    9487904, 15018925, 14655972, 1137437, 4503327, 9470128, 816252, 13494756, 13248834,
    9012464, 14705891, 6370431, 6776633, 58368]
      (monsterCo1GeometryBinaryOperatorMasks 6)
    ![4353777, 9470999, 4360784, 11585115, 12758848, 5400599, 13805943, 81, 1049110, 1089798,
    1099686, 15149499, 6267051, 1267803, 12892037, 9470630, 816298, 13626354, 4729105, 9013027,
    6317679, 14759292, 15165104, 8446992] hx (monsterCo1GeometryBinaryOperatorMasks_decode 6)
    he (by decide +kernel)
  have hc2 : monsterCo1GeometryVectorPoint133AfterSignMatrix *
    monsterCo1GeometryVectorPoint19InverseMatrix =
    monsterCo1GeometryVectorPoint133AfterInverseMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![4353777, 9470999, 4360784, 11585115, 12758848, 5400599, 13805943, 81, 1049110, 1089798,
    1099686, 15149499, 6267051, 1267803, 12892037, 9470630, 816298, 13626354, 4729105, 9013027,
    6317679, 14759292, 15165104, 8446992]
    ![534, 10952565, 4365618, 6678701, 8390307, 1089, 8389685, 241, 7774219, 8423168, 8869733,
    12702185, 9037574, 480068, 8868407, 8869398, 2004638, 12851129, 3736561, 9552297, 8422503,
    16163846, 4308884, 8867938]
    ![12823778, 6443908, 4434500, 3429151, 11688111, 2193954, 5279262, 128, 6653827, 9675641,
    1341151, 2169949, 15830176, 5740224, 12968424, 15041508, 14975008, 2298973, 14702638,
    5847055, 3187212, 7793930, 13900323, 8869569] he hxi hf (by decide +kernel)
  have hc3 : monsterCo1GeometryVectorPoint133AfterInverseMatrix *
    monsterCo1GeometryVectorPoint85Matrix = monsterCo1GeometryVectorPoint133Matrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![12823778, 6443908, 4434500, 3429151, 11688111, 2193954, 5279262, 128, 6653827, 9675641,
    1341151, 2169949, 15830176, 5740224, 12968424, 15041508, 14975008, 2298973, 14702638,
    5847055, 3187212, 7793930, 13900323, 8869569]
    ![58529, 1790917, 10162478, 759097, 8445968, 57424, 8446144, 8389696, 8390352, 42848,
    8389632, 144950, 9167138, 1050214, 9454365, 8430026, 8027952, 13794504, 11072359, 5021406,
    3170570, 33287, 3037368, 1136]
    ![9412031, 8171670, 1023060, 573574, 15784159, 6847405, 1522412, 8389696, 15196598,
    8647046, 1614519, 14896709, 15120153, 9817637, 7840535, 6768412, 420914, 3343547, 12352836,
    3816029, 3172310, 7742129, 2419173, 10220945] hf hy hc (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_line_products
    monsterCo1GeometryVectorPoint19Transport monsterCo1GeometryVectorPoint85Transport 6
    monsterCo1GeometryVectorPoint19Matrix monsterCo1GeometryVectorPoint19InverseMatrix
    monsterCo1GeometryVectorPoint85Matrix
    monsterCo1GeometryVectorPoint133AfterSignMatrix
    monsterCo1GeometryVectorPoint133AfterInverseMatrix monsterCo1GeometryVectorPoint133Matrix
    monsterCo1GeometryVectorPoint19Transport_binary
    monsterCo1GeometryVectorPoint19Transport_inverse_binary
    monsterCo1GeometryVectorPoint85Transport_binary
    hc1 hc2 hc3 v

/-- Source point 133 is the literal actual transported frame point. -/
def monsterCo1GeometryVectorPoint133 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryVectorPoint133Transport • monsterCo1GeometryBasePoint

/-- Complete binary coordinates of this literal actual source point. -/
theorem monsterCo1GeometryVectorPoint133_binary :
    monsterCo1GeometryVectorPoint133.val =
      ![1, 0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0] := by
  change co1BinaryAction monsterCo1GeometryVectorPoint133Transport monsterCo1GeometryBasePoint.val =
      _
  rw [monsterCo1GeometryVectorPoint133Transport_binary, monsterCo1GeometryBasePoint_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
