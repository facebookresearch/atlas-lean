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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint015
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint155

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The literal actual two-core word for source point 163. -/
def monsterCo1GeometryVectorPoint163Transport : Co1 :=
  monsterCo1GeometryVectorPoint15Transport * monsterCo1GeometryTransportOperator 1 *
    monsterCo1GeometryVectorPoint15Transport⁻¹ * monsterCo1GeometryVectorPoint155Transport

/-- Complete displayed binary matrix of actual transport 163. -/
def monsterCo1GeometryVectorPoint163Matrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![3196566, 8439328, 14705890, 5453296, 15575284, 7188458, 6442685, 6121965, 13782278,
      13782312, 816576, 5764189, 55262, 9992620, 16771309, 7560033, 9558379, 5916062, 14898713,
      7336357, 4353912, 8737585, 10747208, 4138018]

/-- First complete finite matrix product in literal actual transport 163. -/
def monsterCo1GeometryVectorPoint163AfterSignMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![49312, 34000, 11560144, 10511568, 12606543, 12631102, 4226255, 12614686, 4250767,
      12639278, 9438208, 14068327, 14571560, 4587042, 8748355, 8773491, 259130, 9983098,
      13772856, 12382375, 1135644, 14953554, 343171, 8445952]

/-- Second complete finite matrix product in literal actual transport 163. -/
def monsterCo1GeometryVectorPoint163AfterInverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![1, 1038, 12616549, 12599785, 2754271, 9766060, 2753155, 9765900, 2753475, 9766540, 50816,
      2805085, 9819934, 1384657, 11234657, 11251041, 8454467, 181900, 9553694, 7831842,
      9488093, 7684449, 15411565, 8389644]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 24000000 in
-- Check every entry of this finite actual transport matrix in the Lean kernel.
/-- Every column of transport 163 is its actual Conway binary action. -/
theorem monsterCo1GeometryVectorPoint163Transport_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint163Transport v =
      monsterCo1GeometryVectorPoint163Matrix *ᵥ v := by
  have hx : monsterCo1GeometryVectorPoint15Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![49312, 8421584, 11560912, 10511824, 12601423, 12627006, 12610767, 12610590, 12635279,
    12635182, 9438720, 5683319, 6180408, 12970498, 355693, 380765, 8646666, 1593978, 5389864,
    12384167, 9523772, 6568274, 338093, 58368] := by decide +kernel
  have hxi : monsterCo1GeometryVectorPoint15InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![8389616, 9359062, 4053439, 11679898, 1310, 8388689, 8390287, 161, 12599777, 49792,
    12517955, 8380818, 9766028, 12518066, 12518796, 4130173, 9102121, 10622437, 8774188,
    1373312, 49804, 4211179, 8308941, 12518991] := by decide +kernel
  have hy : monsterCo1GeometryVectorPoint155Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![3196566, 4186866, 3195142, 8390493, 12517858, 8398589, 9421689, 11591930, 4178114,
    4179007, 1041033, 12184016, 5368402, 4903060, 13590616, 4445140, 11468356, 15136261,
    11692949, 29760, 8312862, 314457, 2904367, 8388848] := by rfl
  have he : monsterCo1GeometryVectorPoint163AfterSignMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![49312, 34000, 11560144, 10511568, 12606543, 12631102, 4226255, 12614686, 4250767,
    12639278, 9438208, 14068327, 14571560, 4587042, 8748355, 8773491, 259130, 9983098,
    13772856, 12382375, 1135644, 14953554, 343171, 8445952] := by rfl
  have hf : monsterCo1GeometryVectorPoint163AfterInverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![1, 1038, 12616549, 12599785, 2754271, 9766060, 2753155, 9765900, 2753475, 9766540, 50816,
    2805085, 9819934, 1384657, 11234657, 11251041, 8454467, 181900, 9553694, 7831842, 9488093,
    7684449, 15411565, 8389644] := by rfl
  have hc : monsterCo1GeometryVectorPoint163Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![3196566, 8439328, 14705890, 5453296, 15575284, 7188458, 6442685, 6121965, 13782278,
    13782312, 816576, 5764189, 55262, 9992620, 16771309, 7560033, 9558379, 5916062, 14898713,
    7336357, 4353912, 8737585, 10747208, 4138018] := by rfl
  have hc1 : monsterCo1GeometryVectorPoint15Matrix *
    monsterCo1GeometryTransportOperatorMatrix 1 =
    monsterCo1GeometryVectorPoint163AfterSignMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![49312, 8421584, 11560912, 10511824, 12601423, 12627006, 12610767, 12610590, 12635279,
    12635182, 9438720, 5683319, 6180408, 12970498, 355693, 380765, 8646666, 1593978, 5389864,
    12384167, 9523772, 6568274, 338093, 58368]
      (monsterCo1GeometryBinaryOperatorMasks 1)
    ![49312, 34000, 11560144, 10511568, 12606543, 12631102, 4226255, 12614686, 4250767,
    12639278, 9438208, 14068327, 14571560, 4587042, 8748355, 8773491, 259130, 9983098,
    13772856, 12382375, 1135644, 14953554, 343171, 8445952] hx
    (monsterCo1GeometryBinaryOperatorMasks_decode 1) he (by decide +kernel)
  have hc2 : monsterCo1GeometryVectorPoint163AfterSignMatrix *
    monsterCo1GeometryVectorPoint15InverseMatrix =
    monsterCo1GeometryVectorPoint163AfterInverseMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![49312, 34000, 11560144, 10511568, 12606543, 12631102, 4226255, 12614686, 4250767,
    12639278, 9438208, 14068327, 14571560, 4587042, 8748355, 8773491, 259130, 9983098,
    13772856, 12382375, 1135644, 14953554, 343171, 8445952]
    ![8389616, 9359062, 4053439, 11679898, 1310, 8388689, 8390287, 161, 12599777, 49792,
    12517955, 8380818, 9766028, 12518066, 12518796, 4130173, 9102121, 10622437, 8774188,
    1373312, 49804, 4211179, 8308941, 12518991]
    ![1, 1038, 12616549, 12599785, 2754271, 9766060, 2753155, 9765900, 2753475, 9766540, 50816,
    2805085, 9819934, 1384657, 11234657, 11251041, 8454467, 181900, 9553694, 7831842, 9488093,
    7684449, 15411565, 8389644] he hxi hf (by decide +kernel)
  have hc3 : monsterCo1GeometryVectorPoint163AfterInverseMatrix *
    monsterCo1GeometryVectorPoint155Matrix = monsterCo1GeometryVectorPoint163Matrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![1, 1038, 12616549, 12599785, 2754271, 9766060, 2753155, 9765900, 2753475, 9766540, 50816,
    2805085, 9819934, 1384657, 11234657, 11251041, 8454467, 181900, 9553694, 7831842, 9488093,
    7684449, 15411565, 8389644]
    ![3196566, 4186866, 3195142, 8390493, 12517858, 8398589, 9421689, 11591930, 4178114,
    4179007, 1041033, 12184016, 5368402, 4903060, 13590616, 4445140, 11468356, 15136261,
    11692949, 29760, 8312862, 314457, 2904367, 8388848]
    ![3196566, 8439328, 14705890, 5453296, 15575284, 7188458, 6442685, 6121965, 13782278,
    13782312, 816576, 5764189, 55262, 9992620, 16771309, 7560033, 9558379, 5916062, 14898713,
    7336357, 4353912, 8737585, 10747208, 4138018] hf hy hc (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_line_products
    monsterCo1GeometryVectorPoint15Transport monsterCo1GeometryVectorPoint155Transport 1
    monsterCo1GeometryVectorPoint15Matrix monsterCo1GeometryVectorPoint15InverseMatrix
    monsterCo1GeometryVectorPoint155Matrix
    monsterCo1GeometryVectorPoint163AfterSignMatrix
    monsterCo1GeometryVectorPoint163AfterInverseMatrix monsterCo1GeometryVectorPoint163Matrix
    monsterCo1GeometryVectorPoint15Transport_binary
    monsterCo1GeometryVectorPoint15Transport_inverse_binary
    monsterCo1GeometryVectorPoint155Transport_binary
    hc1 hc2 hc3 v

/-- Source point 163 is the literal actual transported frame point. -/
def monsterCo1GeometryVectorPoint163 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryVectorPoint163Transport • monsterCo1GeometryBasePoint

/-- Complete binary coordinates of this literal actual source point. -/
theorem monsterCo1GeometryVectorPoint163_binary :
    monsterCo1GeometryVectorPoint163.val =
      ![0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 0] := by
  change co1BinaryAction monsterCo1GeometryVectorPoint163Transport monsterCo1GeometryBasePoint.val =
      _
  rw [monsterCo1GeometryVectorPoint163Transport_binary, monsterCo1GeometryBasePoint_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
