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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint071
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint075

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The literal actual two-core word for source point 124. -/
def monsterCo1GeometryVectorPoint124Transport : Co1 :=
  monsterCo1GeometryVectorPoint71Transport * monsterCo1GeometryTransportOperator 5 *
    monsterCo1GeometryVectorPoint71Transport⁻¹ * monsterCo1GeometryVectorPoint75Transport

/-- Complete displayed binary matrix of actual transport 124. -/
def monsterCo1GeometryVectorPoint124Matrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![8446993, 8881459, 10969406, 2580537, 492770, 26512, 459397, 25408, 492629, 57584,
      8423344, 1183861, 9005009, 9352195, 7903790, 16259737, 5336005, 4528378, 4271535,
      6914150, 1995560, 2489368, 5066898, 8388784]

/-- First complete finite matrix product in literal actual transport 124. -/
def monsterCo1GeometryVectorPoint124AfterSignMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![63040, 63168, 8406528, 8422912, 8393008, 13248, 8441984, 12288, 8442528, 12928, 8438400,
      5620396, 2765919, 4142335, 12652004, 12652392, 77952, 9506816, 193411, 16148957, 258624,
      7514863, 5585571, 8389632]

/-- Second complete finite matrix product in literal actual transport 124. -/
def monsterCo1GeometryVectorPoint124AfterInverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![1, 2, 1896, 1508, 979, 672, 1935, 512, 1743, 128, 1664, 2048, 1381900, 1385612, 1343651,
      1327267, 66176, 182220, 1163296, 7832638, 376864, 6242353, 5554339, 8388608]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 24000000 in
-- Check every entry of this finite actual transport matrix in the Lean kernel.
/-- Every column of transport 124 is its actual Conway binary action. -/
theorem monsterCo1GeometryVectorPoint124Transport_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint124Transport v =
      monsterCo1GeometryVectorPoint124Matrix *ᵥ v := by
  have hx : monsterCo1GeometryVectorPoint71Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![63040, 63168, 18400, 34144, 8392976, 12608, 53792, 12928, 53248, 12288, 8437760, 5620396,
    11154716, 12531516, 12586475, 12586855, 78336, 1118380, 193420, 7825623, 258639, 7580521,
    5520044, 8389632] := by rfl
  have hxi : monsterCo1GeometryVectorPoint71InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![4142451, 2766803, 13922752, 13939520, 8389554, 963, 8389762, 3, 8390306, 643, 8390284,
    4261903, 908, 396, 8390123, 8390503, 65667, 8701486, 193420, 8938724, 246351, 9205594,
    63503, 1676] := by rfl
  have hy : monsterCo1GeometryVectorPoint75Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![8446993, 8881459, 11003449, 2581646, 57504, 58400, 57456, 57584, 26272, 25408, 8389632,
    1183861, 8860884, 8414390, 10494444, 2138459, 5367925, 12917658, 13631434, 5995357,
    9478477, 9461761, 9825104, 8388784] := by rfl
  have he : monsterCo1GeometryVectorPoint124AfterSignMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![63040, 63168, 8406528, 8422912, 8393008, 13248, 8441984, 12288, 8442528, 12928, 8438400,
    5620396, 2765919, 4142335, 12652004, 12652392, 77952, 9506816, 193411, 16148957, 258624,
    7514863, 5585571, 8389632] := by rfl
  have hf : monsterCo1GeometryVectorPoint124AfterInverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![1, 2, 1896, 1508, 979, 672, 1935, 512, 1743, 128, 1664, 2048, 1381900, 1385612, 1343651,
    1327267, 66176, 182220, 1163296, 7832638, 376864, 6242353, 5554339, 8388608] := by rfl
  have hc : monsterCo1GeometryVectorPoint124Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![8446993, 8881459, 10969406, 2580537, 492770, 26512, 459397, 25408, 492629, 57584,
    8423344, 1183861, 9005009, 9352195, 7903790, 16259737, 5336005, 4528378, 4271535, 6914150,
    1995560, 2489368, 5066898, 8388784] := by rfl
  have hc1 : monsterCo1GeometryVectorPoint71Matrix *
    monsterCo1GeometryTransportOperatorMatrix 5 =
    monsterCo1GeometryVectorPoint124AfterSignMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![63040, 63168, 18400, 34144, 8392976, 12608, 53792, 12928, 53248, 12288, 8437760, 5620396,
    11154716, 12531516, 12586475, 12586855, 78336, 1118380, 193420, 7825623, 258639, 7580521,
    5520044, 8389632]
      (monsterCo1GeometryBinaryOperatorMasks 5)
    ![63040, 63168, 8406528, 8422912, 8393008, 13248, 8441984, 12288, 8442528, 12928, 8438400,
    5620396, 2765919, 4142335, 12652004, 12652392, 77952, 9506816, 193411, 16148957, 258624,
    7514863, 5585571, 8389632] hx (monsterCo1GeometryBinaryOperatorMasks_decode 5) he (by
    decide +kernel)
  have hc2 : monsterCo1GeometryVectorPoint124AfterSignMatrix *
    monsterCo1GeometryVectorPoint71InverseMatrix =
    monsterCo1GeometryVectorPoint124AfterInverseMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![63040, 63168, 8406528, 8422912, 8393008, 13248, 8441984, 12288, 8442528, 12928, 8438400,
    5620396, 2765919, 4142335, 12652004, 12652392, 77952, 9506816, 193411, 16148957, 258624,
    7514863, 5585571, 8389632]
    ![4142451, 2766803, 13922752, 13939520, 8389554, 963, 8389762, 3, 8390306, 643, 8390284,
    4261903, 908, 396, 8390123, 8390503, 65667, 8701486, 193420, 8938724, 246351, 9205594,
    63503, 1676]
    ![1, 2, 1896, 1508, 979, 672, 1935, 512, 1743, 128, 1664, 2048, 1381900, 1385612, 1343651,
    1327267, 66176, 182220, 1163296, 7832638, 376864, 6242353, 5554339, 8388608] he hxi hf (by
    decide +kernel)
  have hc3 : monsterCo1GeometryVectorPoint124AfterInverseMatrix *
    monsterCo1GeometryVectorPoint75Matrix = monsterCo1GeometryVectorPoint124Matrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![1, 2, 1896, 1508, 979, 672, 1935, 512, 1743, 128, 1664, 2048, 1381900, 1385612, 1343651,
    1327267, 66176, 182220, 1163296, 7832638, 376864, 6242353, 5554339, 8388608]
    ![8446993, 8881459, 11003449, 2581646, 57504, 58400, 57456, 57584, 26272, 25408, 8389632,
    1183861, 8860884, 8414390, 10494444, 2138459, 5367925, 12917658, 13631434, 5995357,
    9478477, 9461761, 9825104, 8388784]
    ![8446993, 8881459, 10969406, 2580537, 492770, 26512, 459397, 25408, 492629, 57584,
    8423344, 1183861, 9005009, 9352195, 7903790, 16259737, 5336005, 4528378, 4271535, 6914150,
    1995560, 2489368, 5066898, 8388784] hf hy hc (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_line_products
    monsterCo1GeometryVectorPoint71Transport monsterCo1GeometryVectorPoint75Transport 5
    monsterCo1GeometryVectorPoint71Matrix monsterCo1GeometryVectorPoint71InverseMatrix
    monsterCo1GeometryVectorPoint75Matrix
    monsterCo1GeometryVectorPoint124AfterSignMatrix
    monsterCo1GeometryVectorPoint124AfterInverseMatrix monsterCo1GeometryVectorPoint124Matrix
    monsterCo1GeometryVectorPoint71Transport_binary
    monsterCo1GeometryVectorPoint71Transport_inverse_binary
    monsterCo1GeometryVectorPoint75Transport_binary
    hc1 hc2 hc3 v

/-- Source point 124 is the literal actual transported frame point. -/
def monsterCo1GeometryVectorPoint124 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryVectorPoint124Transport • monsterCo1GeometryBasePoint

/-- Complete binary coordinates of this literal actual source point. -/
theorem monsterCo1GeometryVectorPoint124_binary :
    monsterCo1GeometryVectorPoint124.val =
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 0, 1, 0, 0] := by
  change co1BinaryAction monsterCo1GeometryVectorPoint124Transport monsterCo1GeometryBasePoint.val =
      _
  rw [monsterCo1GeometryVectorPoint124Transport_binary, monsterCo1GeometryBasePoint_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
