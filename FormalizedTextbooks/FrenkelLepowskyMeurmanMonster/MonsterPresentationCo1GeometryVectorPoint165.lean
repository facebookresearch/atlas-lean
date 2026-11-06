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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint141
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint155

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The literal actual two-core word for source point 165. -/
def monsterCo1GeometryVectorPoint165Transport : Co1 :=
  monsterCo1GeometryVectorPoint141Transport * monsterCo1GeometryTransportOperator 1 *
    monsterCo1GeometryVectorPoint141Transport⁻¹ * monsterCo1GeometryVectorPoint155Transport

/-- Complete displayed binary matrix of actual transport 165. -/
def monsterCo1GeometryVectorPoint165Matrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![3196566, 4186866, 14647885, 6033768, 6131438, 14519565, 5400663, 15551242, 14503886,
      6114285, 234453, 11009954, 14288, 10758887, 9231092, 792612, 16685822, 9024912, 33792,
      29760, 10712851, 5549038, 11795894, 12526802]

/-- First complete finite matrix product in literal actual transport 165. -/
def monsterCo1GeometryVectorPoint165AfterSignMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![49312, 8414416, 3179728, 2131152, 12606543, 12631102, 4226255, 12614686, 12598415,
      4209710, 1106944, 14906041, 6174809, 14016034, 2457010, 11878178, 3396811, 3707947,
      7530601, 9228374, 12692626, 11850877, 8780930, 8445952]

/-- Second complete finite matrix product in literal actual transport 165. -/
def monsterCo1GeometryVectorPoint165AfterInverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![1, 2, 4228111, 12600959, 2753314, 9765457, 11143038, 9765617, 2753074, 1377405, 49776,
      951826, 2806864, 9822300, 2411570, 2411074, 16678919, 8225092, 7243307, 524288, 328224,
      14648648, 10799685, 1036]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 24000000 in
-- Check every entry of this finite actual transport matrix in the Lean kernel.
/-- Every column of transport 165 is its actual Conway binary action. -/
theorem monsterCo1GeometryVectorPoint165Transport_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint165Transport v =
      monsterCo1GeometryVectorPoint165Matrix *ᵥ v := by
  have hx : monsterCo1GeometryVectorPoint141Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![49312, 8414416, 11568080, 10518992, 12601423, 12627006, 12610767, 12610590, 12593295,
    12593198, 9495040, 6517639, 6172233, 14011394, 2452636, 3483660, 11786235, 3707691,
    7536505, 9228374, 12696754, 3463037, 387244, 58368] := by rfl
  have hxi : monsterCo1GeometryVectorPoint141InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![8389616, 16657741, 13450966, 4382706, 8389918, 8388689, 1679, 161, 4211323, 8438396,
    12517699, 8380818, 9765489, 12517810, 12519052, 4130429, 713684, 2234224, 385745, 9762068,
    8438384, 12599921, 928599, 4130127] := by rfl
  have hy : monsterCo1GeometryVectorPoint155Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![3196566, 4186866, 3195142, 8390493, 12517858, 8398589, 9421689, 11591930, 4178114,
    4179007, 1041033, 12184016, 5368402, 4903060, 13590616, 4445140, 11468356, 15136261,
    11692949, 29760, 8312862, 314457, 2904367, 8388848] := by rfl
  have he : monsterCo1GeometryVectorPoint165AfterSignMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![49312, 8414416, 3179728, 2131152, 12606543, 12631102, 4226255, 12614686, 12598415,
    4209710, 1106944, 14906041, 6174809, 14016034, 2457010, 11878178, 3396811, 3707947,
    7530601, 9228374, 12692626, 11850877, 8780930, 8445952] := by rfl
  have hf : monsterCo1GeometryVectorPoint165AfterInverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![1, 2, 4228111, 12600959, 2753314, 9765457, 11143038, 9765617, 2753074, 1377405, 49776,
    951826, 2806864, 9822300, 2411570, 2411074, 16678919, 8225092, 7243307, 524288, 328224,
    14648648, 10799685, 1036] := by rfl
  have hc : monsterCo1GeometryVectorPoint165Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![3196566, 4186866, 14647885, 6033768, 6131438, 14519565, 5400663, 15551242, 14503886,
    6114285, 234453, 11009954, 14288, 10758887, 9231092, 792612, 16685822, 9024912, 33792,
    29760, 10712851, 5549038, 11795894, 12526802] := by rfl
  have hc1 : monsterCo1GeometryVectorPoint141Matrix *
    monsterCo1GeometryTransportOperatorMatrix 1 =
    monsterCo1GeometryVectorPoint165AfterSignMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![49312, 8414416, 11568080, 10518992, 12601423, 12627006, 12610767, 12610590, 12593295,
    12593198, 9495040, 6517639, 6172233, 14011394, 2452636, 3483660, 11786235, 3707691,
    7536505, 9228374, 12696754, 3463037, 387244, 58368]
      (monsterCo1GeometryBinaryOperatorMasks 1)
    ![49312, 8414416, 3179728, 2131152, 12606543, 12631102, 4226255, 12614686, 12598415,
    4209710, 1106944, 14906041, 6174809, 14016034, 2457010, 11878178, 3396811, 3707947,
    7530601, 9228374, 12692626, 11850877, 8780930, 8445952] hx
    (monsterCo1GeometryBinaryOperatorMasks_decode 1) he (by decide +kernel)
  have hc2 : monsterCo1GeometryVectorPoint165AfterSignMatrix *
    monsterCo1GeometryVectorPoint141InverseMatrix =
    monsterCo1GeometryVectorPoint165AfterInverseMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![49312, 8414416, 3179728, 2131152, 12606543, 12631102, 4226255, 12614686, 12598415,
    4209710, 1106944, 14906041, 6174809, 14016034, 2457010, 11878178, 3396811, 3707947,
    7530601, 9228374, 12692626, 11850877, 8780930, 8445952]
    ![8389616, 16657741, 13450966, 4382706, 8389918, 8388689, 1679, 161, 4211323, 8438396,
    12517699, 8380818, 9765489, 12517810, 12519052, 4130429, 713684, 2234224, 385745, 9762068,
    8438384, 12599921, 928599, 4130127]
    ![1, 2, 4228111, 12600959, 2753314, 9765457, 11143038, 9765617, 2753074, 1377405, 49776,
    951826, 2806864, 9822300, 2411570, 2411074, 16678919, 8225092, 7243307, 524288, 328224,
    14648648, 10799685, 1036] he hxi hf (by decide +kernel)
  have hc3 : monsterCo1GeometryVectorPoint165AfterInverseMatrix *
    monsterCo1GeometryVectorPoint155Matrix = monsterCo1GeometryVectorPoint165Matrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![1, 2, 4228111, 12600959, 2753314, 9765457, 11143038, 9765617, 2753074, 1377405, 49776,
    951826, 2806864, 9822300, 2411570, 2411074, 16678919, 8225092, 7243307, 524288, 328224,
    14648648, 10799685, 1036]
    ![3196566, 4186866, 3195142, 8390493, 12517858, 8398589, 9421689, 11591930, 4178114,
    4179007, 1041033, 12184016, 5368402, 4903060, 13590616, 4445140, 11468356, 15136261,
    11692949, 29760, 8312862, 314457, 2904367, 8388848]
    ![3196566, 4186866, 14647885, 6033768, 6131438, 14519565, 5400663, 15551242, 14503886,
    6114285, 234453, 11009954, 14288, 10758887, 9231092, 792612, 16685822, 9024912, 33792,
    29760, 10712851, 5549038, 11795894, 12526802] hf hy hc (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_line_products
    monsterCo1GeometryVectorPoint141Transport monsterCo1GeometryVectorPoint155Transport 1
    monsterCo1GeometryVectorPoint141Matrix monsterCo1GeometryVectorPoint141InverseMatrix
    monsterCo1GeometryVectorPoint155Matrix
    monsterCo1GeometryVectorPoint165AfterSignMatrix
    monsterCo1GeometryVectorPoint165AfterInverseMatrix monsterCo1GeometryVectorPoint165Matrix
    monsterCo1GeometryVectorPoint141Transport_binary
    monsterCo1GeometryVectorPoint141Transport_inverse_binary
    monsterCo1GeometryVectorPoint155Transport_binary
    hc1 hc2 hc3 v

/-- Source point 165 is the literal actual transported frame point. -/
def monsterCo1GeometryVectorPoint165 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryVectorPoint165Transport • monsterCo1GeometryBasePoint

/-- Complete binary coordinates of this literal actual source point. -/
theorem monsterCo1GeometryVectorPoint165_binary :
    monsterCo1GeometryVectorPoint165.val =
      ![0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 0] := by
  change co1BinaryAction monsterCo1GeometryVectorPoint165Transport monsterCo1GeometryBasePoint.val =
      _
  rw [monsterCo1GeometryVectorPoint165Transport_binary, monsterCo1GeometryBasePoint_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
