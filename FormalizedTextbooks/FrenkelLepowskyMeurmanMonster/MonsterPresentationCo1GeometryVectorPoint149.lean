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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint045
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint120

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The literal actual two-core word for source point 149. -/
def monsterCo1GeometryVectorPoint149Transport : Co1 :=
  monsterCo1GeometryVectorPoint45Transport * monsterCo1GeometryTransportOperator 7 *
    monsterCo1GeometryVectorPoint45Transport⁻¹ * monsterCo1GeometryVectorPoint120Transport

/-- Complete displayed binary matrix of actual transport 149. -/
def monsterCo1GeometryVectorPoint149Matrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![9090233, 58449, 2814979, 11195406, 51088, 1456, 8447120, 64, 49968, 432, 8389632,
      9537278, 49788, 9093316, 2146998, 2154683, 9982584, 6551685, 54130, 9778562, 10024722,
      15956927, 2104548, 1104]

/-- First complete finite matrix product in literal actual transport 149. -/
def monsterCo1GeometryVectorPoint149AfterSignMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![2803008, 11191378, 10670896, 10670908, 53792, 336, 5936, 16, 5392, 8388624, 8389632,
      11985413, 11154830, 2765852, 2265262, 2266930, 122, 315794, 182010, 7601525, 8570195,
      6437093, 6476325, 272]

/-- Second complete finite matrix product in literal actual transport 149. -/
def monsterCo1GeometryVectorPoint149AfterInverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![2, 1, 8388616, 8388612, 336, 672, 64, 128, 256, 512, 1024, 52236, 8192, 4096, 8422400,
      8406016, 66176, 131392, 328352, 655696, 1114784, 2228560, 12582924, 8388608]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 24000000 in
-- Check every entry of this finite actual transport matrix in the Lean kernel.
/-- Every column of transport 149 is its actual Conway binary action. -/
theorem monsterCo1GeometryVectorPoint149Transport_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint149Transport v =
      monsterCo1GeometryVectorPoint149Matrix *ᵥ v := by
  have hx : monsterCo1GeometryVectorPoint45Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![11191378, 2803008, 10670636, 10670624, 53248, 8388944, 5936, 16, 5392, 8388624, 8389632,
    3596693, 2765852, 11154830, 10654242, 10655166, 8388730, 316338, 8570832, 7863527, 181369,
    6699383, 6476601, 272] := by decide +kernel
  have hxi : monsterCo1GeometryVectorPoint45InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![1427119, 8389251, 8517088, 8517100, 128, 8452047, 8389280, 12291, 8388736, 8451727, 1664,
    6475870, 8390528, 4798, 8405643, 17691, 12459897, 313276, 144336, 8388842, 9842282, 312420,
    5517771, 640] := by decide +kernel
  have hy : monsterCo1GeometryVectorPoint120Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![58449, 9090233, 11194462, 2814035, 8446000, 1088, 8447120, 64, 49968, 432, 8389632,
    9535742, 9093316, 49788, 10543339, 10535654, 9982856, 14933797, 9995594, 7744823, 41258,
    1073930, 10500281, 1104] := by rfl
  have he : monsterCo1GeometryVectorPoint149AfterSignMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![2803008, 11191378, 10670896, 10670908, 53792, 336, 5936, 16, 5392, 8388624, 8389632,
    11985413, 11154830, 2765852, 2265262, 2266930, 122, 315794, 182010, 7601525, 8570195,
    6437093, 6476325, 272] := by rfl
  have hf : monsterCo1GeometryVectorPoint149AfterInverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![2, 1, 8388616, 8388612, 336, 672, 64, 128, 256, 512, 1024, 52236, 8192, 4096, 8422400,
    8406016, 66176, 131392, 328352, 655696, 1114784, 2228560, 12582924, 8388608] := by rfl
  have hc : monsterCo1GeometryVectorPoint149Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![9090233, 58449, 2814979, 11195406, 51088, 1456, 8447120, 64, 49968, 432, 8389632,
    9537278, 49788, 9093316, 2146998, 2154683, 9982584, 6551685, 54130, 9778562, 10024722,
    15956927, 2104548, 1104] := by rfl
  have hc1 : monsterCo1GeometryVectorPoint45Matrix *
    monsterCo1GeometryTransportOperatorMatrix 7 =
    monsterCo1GeometryVectorPoint149AfterSignMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![11191378, 2803008, 10670636, 10670624, 53248, 8388944, 5936, 16, 5392, 8388624, 8389632,
    3596693, 2765852, 11154830, 10654242, 10655166, 8388730, 316338, 8570832, 7863527, 181369,
    6699383, 6476601, 272]
      (monsterCo1GeometryBinaryOperatorMasks 7)
    ![2803008, 11191378, 10670896, 10670908, 53792, 336, 5936, 16, 5392, 8388624, 8389632,
    11985413, 11154830, 2765852, 2265262, 2266930, 122, 315794, 182010, 7601525, 8570195,
    6437093, 6476325, 272] hx (monsterCo1GeometryBinaryOperatorMasks_decode 7) he
      (by decide +kernel)
  have hc2 : monsterCo1GeometryVectorPoint149AfterSignMatrix *
    monsterCo1GeometryVectorPoint45InverseMatrix =
    monsterCo1GeometryVectorPoint149AfterInverseMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![2803008, 11191378, 10670896, 10670908, 53792, 336, 5936, 16, 5392, 8388624, 8389632,
    11985413, 11154830, 2765852, 2265262, 2266930, 122, 315794, 182010, 7601525, 8570195,
    6437093, 6476325, 272]
    ![1427119, 8389251, 8517088, 8517100, 128, 8452047, 8389280, 12291, 8388736, 8451727, 1664,
    6475870, 8390528, 4798, 8405643, 17691, 12459897, 313276, 144336, 8388842, 9842282, 312420,
    5517771, 640]
    ![2, 1, 8388616, 8388612, 336, 672, 64, 128, 256, 512, 1024, 52236, 8192, 4096, 8422400,
    8406016, 66176, 131392, 328352, 655696, 1114784, 2228560, 12582924, 8388608] he hxi hf (by
    decide +kernel)
  have hc3 : monsterCo1GeometryVectorPoint149AfterInverseMatrix *
    monsterCo1GeometryVectorPoint120Matrix = monsterCo1GeometryVectorPoint149Matrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![2, 1, 8388616, 8388612, 336, 672, 64, 128, 256, 512, 1024, 52236, 8192, 4096, 8422400,
    8406016, 66176, 131392, 328352, 655696, 1114784, 2228560, 12582924, 8388608]
    ![58449, 9090233, 11194462, 2814035, 8446000, 1088, 8447120, 64, 49968, 432, 8389632,
    9535742, 9093316, 49788, 10543339, 10535654, 9982856, 14933797, 9995594, 7744823, 41258,
    1073930, 10500281, 1104]
    ![9090233, 58449, 2814979, 11195406, 51088, 1456, 8447120, 64, 49968, 432, 8389632,
    9537278, 49788, 9093316, 2146998, 2154683, 9982584, 6551685, 54130, 9778562, 10024722,
    15956927, 2104548, 1104] hf hy hc (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_line_products
    monsterCo1GeometryVectorPoint45Transport monsterCo1GeometryVectorPoint120Transport 7
    monsterCo1GeometryVectorPoint45Matrix monsterCo1GeometryVectorPoint45InverseMatrix
    monsterCo1GeometryVectorPoint120Matrix
    monsterCo1GeometryVectorPoint149AfterSignMatrix
    monsterCo1GeometryVectorPoint149AfterInverseMatrix monsterCo1GeometryVectorPoint149Matrix
    monsterCo1GeometryVectorPoint45Transport_binary
    monsterCo1GeometryVectorPoint45Transport_inverse_binary
    monsterCo1GeometryVectorPoint120Transport_binary
    hc1 hc2 hc3 v

/-- Source point 149 is the literal actual transported frame point. -/
def monsterCo1GeometryVectorPoint149 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryVectorPoint149Transport • monsterCo1GeometryBasePoint

/-- Complete binary coordinates of this literal actual source point. -/
theorem monsterCo1GeometryVectorPoint149_binary :
    monsterCo1GeometryVectorPoint149.val =
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0] := by
  change co1BinaryAction monsterCo1GeometryVectorPoint149Transport monsterCo1GeometryBasePoint.val =
      _
  rw [monsterCo1GeometryVectorPoint149Transport_binary, monsterCo1GeometryBasePoint_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
