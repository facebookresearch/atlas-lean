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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint007
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint084

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The literal actual two-core word for source point 132. -/
def monsterCo1GeometryVectorPoint132Transport : Co1 :=
  monsterCo1GeometryVectorPoint7Transport * monsterCo1GeometryTransportOperator 5 *
    monsterCo1GeometryVectorPoint7Transport⁻¹ * monsterCo1GeometryVectorPoint84Transport

/-- Complete displayed binary matrix of actual transport 132. -/
def monsterCo1GeometryVectorPoint132Matrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![2811377, 1431054, 5779058, 5828222, 5904, 9632, 4608, 9712, 5424, 8447152, 8389632,
      7330815, 1378226, 2810141, 15187681, 15187533, 16616647, 11751755, 14503035, 9552546,
      713996, 10654663, 13460932, 8439216]

/-- First complete finite matrix product in literal actual transport 132. -/
def monsterCo1GeometryVectorPoint132AfterSignMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![12517811, 11142035, 5507624, 5507620, 54192, 13248, 8441984, 12288, 8442528, 12928,
      8389632, 4261903, 11190303, 12566591, 12667364, 12684136, 77952, 8704684, 144271,
      8966310, 209484, 840600, 67599, 50816]

/-- Second complete finite matrix product in literal actual transport 132. -/
def monsterCo1GeometryVectorPoint132AfterInverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![9815181, 9815566, 1323563, 1323559, 13267, 672, 8451983, 512, 8451791, 128, 1024,
      1325231, 9819276, 9823756, 9745731, 9729987, 66176, 8570816, 1114156, 12000313, 327724,
      2091066, 5517487, 8389248]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 24000000 in
-- Check every entry of this finite actual transport matrix in the Lean kernel.
/-- Every column of transport 132 is its actual Conway binary action. -/
theorem monsterCo1GeometryVectorPoint132Transport_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint132Transport v =
      monsterCo1GeometryVectorPoint132Matrix *ᵥ v := by
  have hx : monsterCo1GeometryVectorPoint7Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![4129008, 2752592, 5572775, 5572779, 53520, 12608, 53792, 12928, 53248, 12288, 8389632,
    4196352, 2802012, 4178940, 4212747, 4229127, 78336, 315904, 143616, 577792, 209091, 839730,
    2048, 50176] := by decide +kernel
  have hxi : monsterCo1GeometryVectorPoint7InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![4129776, 2752848, 1378983, 1378987, 53522, 12611, 53794, 12931, 53250, 12291, 8437772,
    4194304, 49420, 49932, 16395, 32775, 78339, 315906, 143619, 577794, 196803, 786482,
    4196352, 8438796] := by decide +kernel
  have hy : monsterCo1GeometryVectorPoint84Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![58529, 12523038, 1004361, 1020741, 8389680, 8447200, 8388656, 8447152, 8390400, 9712,
    8389632, 12085124, 4130530, 8397069, 3146986, 11584774, 8211847, 3364391, 16223335,
    3392510, 2106640, 34519, 1759679, 1264] := by rfl
  have he : monsterCo1GeometryVectorPoint132AfterSignMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![12517811, 11142035, 5507624, 5507620, 54192, 13248, 8441984, 12288, 8442528, 12928,
    8389632, 4261903, 11190303, 12566591, 12667364, 12684136, 77952, 8704684, 144271, 8966310,
    209484, 840600, 67599, 50816] := by rfl
  have hf : monsterCo1GeometryVectorPoint132AfterInverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![9815181, 9815566, 1323563, 1323559, 13267, 672, 8451983, 512, 8451791, 128, 1024,
    1325231, 9819276, 9823756, 9745731, 9729987, 66176, 8570816, 1114156, 12000313, 327724,
    2091066, 5517487, 8389248] := by rfl
  have hc : monsterCo1GeometryVectorPoint132Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![2811377, 1431054, 5779058, 5828222, 5904, 9632, 4608, 9712, 5424, 8447152, 8389632,
    7330815, 1378226, 2810141, 15187681, 15187533, 16616647, 11751755, 14503035, 9552546,
    713996, 10654663, 13460932, 8439216] := by rfl
  have hc1 : monsterCo1GeometryVectorPoint7Matrix * monsterCo1GeometryTransportOperatorMatrix
    5 = monsterCo1GeometryVectorPoint132AfterSignMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![4129008, 2752592, 5572775, 5572779, 53520, 12608, 53792, 12928, 53248, 12288, 8389632,
    4196352, 2802012, 4178940, 4212747, 4229127, 78336, 315904, 143616, 577792, 209091, 839730,
    2048, 50176]
      (monsterCo1GeometryBinaryOperatorMasks 5)
    ![12517811, 11142035, 5507624, 5507620, 54192, 13248, 8441984, 12288, 8442528, 12928,
    8389632, 4261903, 11190303, 12566591, 12667364, 12684136, 77952, 8704684, 144271, 8966310,
    209484, 840600, 67599, 50816] hx (monsterCo1GeometryBinaryOperatorMasks_decode 5) he (by
    decide +kernel)
  have hc2 : monsterCo1GeometryVectorPoint132AfterSignMatrix *
    monsterCo1GeometryVectorPoint7InverseMatrix =
    monsterCo1GeometryVectorPoint132AfterInverseMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![12517811, 11142035, 5507624, 5507620, 54192, 13248, 8441984, 12288, 8442528, 12928,
    8389632, 4261903, 11190303, 12566591, 12667364, 12684136, 77952, 8704684, 144271, 8966310,
    209484, 840600, 67599, 50816]
    ![4129776, 2752848, 1378983, 1378987, 53522, 12611, 53794, 12931, 53250, 12291, 8437772,
    4194304, 49420, 49932, 16395, 32775, 78339, 315906, 143619, 577794, 196803, 786482,
    4196352, 8438796]
    ![9815181, 9815566, 1323563, 1323559, 13267, 672, 8451983, 512, 8451791, 128, 1024,
    1325231, 9819276, 9823756, 9745731, 9729987, 66176, 8570816, 1114156, 12000313, 327724,
    2091066, 5517487, 8389248] he hxi hf (by decide +kernel)
  have hc3 : monsterCo1GeometryVectorPoint132AfterInverseMatrix *
    monsterCo1GeometryVectorPoint84Matrix = monsterCo1GeometryVectorPoint132Matrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![9815181, 9815566, 1323563, 1323559, 13267, 672, 8451983, 512, 8451791, 128, 1024,
    1325231, 9819276, 9823756, 9745731, 9729987, 66176, 8570816, 1114156, 12000313, 327724,
    2091066, 5517487, 8389248]
    ![58529, 12523038, 1004361, 1020741, 8389680, 8447200, 8388656, 8447152, 8390400, 9712,
    8389632, 12085124, 4130530, 8397069, 3146986, 11584774, 8211847, 3364391, 16223335,
    3392510, 2106640, 34519, 1759679, 1264]
    ![2811377, 1431054, 5779058, 5828222, 5904, 9632, 4608, 9712, 5424, 8447152, 8389632,
    7330815, 1378226, 2810141, 15187681, 15187533, 16616647, 11751755, 14503035, 9552546,
    713996, 10654663, 13460932, 8439216] hf hy hc (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_line_products
    monsterCo1GeometryVectorPoint7Transport monsterCo1GeometryVectorPoint84Transport 5
    monsterCo1GeometryVectorPoint7Matrix monsterCo1GeometryVectorPoint7InverseMatrix
    monsterCo1GeometryVectorPoint84Matrix
    monsterCo1GeometryVectorPoint132AfterSignMatrix
    monsterCo1GeometryVectorPoint132AfterInverseMatrix monsterCo1GeometryVectorPoint132Matrix
    monsterCo1GeometryVectorPoint7Transport_binary
    monsterCo1GeometryVectorPoint7Transport_inverse_binary
    monsterCo1GeometryVectorPoint84Transport_binary
    hc1 hc2 hc3 v

/-- Source point 132 is the literal actual transported frame point. -/
def monsterCo1GeometryVectorPoint132 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryVectorPoint132Transport • monsterCo1GeometryBasePoint

/-- Complete binary coordinates of this literal actual source point. -/
theorem monsterCo1GeometryVectorPoint132_binary :
    monsterCo1GeometryVectorPoint132.val =
      ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0] := by
  change co1BinaryAction monsterCo1GeometryVectorPoint132Transport monsterCo1GeometryBasePoint.val =
      _
  rw [monsterCo1GeometryVectorPoint132Transport_binary, monsterCo1GeometryBasePoint_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
