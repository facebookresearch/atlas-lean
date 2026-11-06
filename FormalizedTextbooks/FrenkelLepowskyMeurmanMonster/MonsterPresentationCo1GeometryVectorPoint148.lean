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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint013
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint109

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The literal actual two-core word for source point 148. -/
def monsterCo1GeometryVectorPoint148Transport : Co1 :=
  monsterCo1GeometryVectorPoint13Transport * monsterCo1GeometryTransportOperator 5 *
    monsterCo1GeometryVectorPoint13Transport⁻¹ * monsterCo1GeometryVectorPoint109Transport

/-- Complete displayed binary matrix of actual transport 148. -/
def monsterCo1GeometryVectorPoint148Matrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![942257, 5583046, 14437001, 13388425, 1425967, 1106647, 377417, 1106439, 8766660, 8445969,
      8388768, 37609, 12588179, 10389200, 9912067, 8863091, 3939936, 2414260, 12360311,
      10001009, 9364166, 16194272, 3290195, 9438823]

/-- First complete finite matrix product in literal actual transport 148. -/
def monsterCo1GeometryVectorPoint148AfterSignMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![12517811, 11142035, 5507624, 5507620, 5424, 13248, 8441984, 12288, 8442528, 12928,
      8389632, 5585571, 11154783, 12531711, 12684932, 12668552, 77952, 9556096, 131331,
      16136509, 197184, 7486127, 67599, 50816]

/-- Second complete finite matrix product in literal actual transport 148. -/
def monsterCo1GeometryVectorPoint148AfterInverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![9815181, 9815566, 1323563, 1323559, 13267, 672, 8451983, 512, 8451791, 128, 1024,
      1325231, 9819276, 9823756, 9745731, 9729987, 66176, 8570816, 1114156, 12000313, 327724,
      2091066, 5517487, 8389248]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 24000000 in
-- Check every entry of this finite actual transport matrix in the Lean kernel.
/-- Every column of transport 148 is its actual Conway binary action. -/
theorem monsterCo1GeometryVectorPoint148Transport_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint148Transport v =
      monsterCo1GeometryVectorPoint148Matrix *ᵥ v := by
  have hx : monsterCo1GeometryVectorPoint13Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![4129008, 2752592, 5572775, 5572779, 5392, 12608, 53792, 12928, 53248, 12288, 8389632,
    5520044, 2765852, 4142140, 4230635, 4214631, 78336, 1168044, 131340, 7813623, 197199,
    7551081, 2048, 50176] := by decide +kernel
  have hxi : monsterCo1GeometryVectorPoint13InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![12518067, 11141779, 1312808, 1312804, 54194, 13251, 8441986, 12291, 8442530, 12931,
    8438412, 4194304, 50060, 49548, 8405483, 8422247, 77955, 8704686, 144268, 8966308, 196812,
    9175352, 4261903, 8439436] := by decide +kernel
  have hy : monsterCo1GeometryVectorPoint109Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![57552, 13349553, 7074506, 8123082, 1152, 8446145, 81, 8445969, 8390364, 1106439, 8388768,
    2566332, 13538546, 1191, 2131900, 10520538, 11279478, 3462808, 11673201, 13246712, 8414912,
    10512106, 1412614, 1137] := by rfl
  have he : monsterCo1GeometryVectorPoint148AfterSignMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![12517811, 11142035, 5507624, 5507620, 5424, 13248, 8441984, 12288, 8442528, 12928,
    8389632, 5585571, 11154783, 12531711, 12684932, 12668552, 77952, 9556096, 131331, 16136509,
    197184, 7486127, 67599, 50816] := by rfl
  have hf : monsterCo1GeometryVectorPoint148AfterInverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![9815181, 9815566, 1323563, 1323559, 13267, 672, 8451983, 512, 8451791, 128, 1024,
    1325231, 9819276, 9823756, 9745731, 9729987, 66176, 8570816, 1114156, 12000313, 327724,
    2091066, 5517487, 8389248] := by rfl
  have hc : monsterCo1GeometryVectorPoint148Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![942257, 5583046, 14437001, 13388425, 1425967, 1106647, 377417, 1106439, 8766660, 8445969,
    8388768, 37609, 12588179, 10389200, 9912067, 8863091, 3939936, 2414260, 12360311, 10001009,
    9364166, 16194272, 3290195, 9438823] := by rfl
  have hc1 : monsterCo1GeometryVectorPoint13Matrix *
    monsterCo1GeometryTransportOperatorMatrix 5 =
    monsterCo1GeometryVectorPoint148AfterSignMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![4129008, 2752592, 5572775, 5572779, 5392, 12608, 53792, 12928, 53248, 12288, 8389632,
    5520044, 2765852, 4142140, 4230635, 4214631, 78336, 1168044, 131340, 7813623, 197199,
    7551081, 2048, 50176]
      (monsterCo1GeometryBinaryOperatorMasks 5)
    ![12517811, 11142035, 5507624, 5507620, 5424, 13248, 8441984, 12288, 8442528, 12928,
    8389632, 5585571, 11154783, 12531711, 12684932, 12668552, 77952, 9556096, 131331, 16136509,
    197184, 7486127, 67599, 50816] hx (monsterCo1GeometryBinaryOperatorMasks_decode 5) he (by
    decide +kernel)
  have hc2 : monsterCo1GeometryVectorPoint148AfterSignMatrix *
    monsterCo1GeometryVectorPoint13InverseMatrix =
    monsterCo1GeometryVectorPoint148AfterInverseMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![12517811, 11142035, 5507624, 5507620, 5424, 13248, 8441984, 12288, 8442528, 12928,
    8389632, 5585571, 11154783, 12531711, 12684932, 12668552, 77952, 9556096, 131331, 16136509,
    197184, 7486127, 67599, 50816]
    ![12518067, 11141779, 1312808, 1312804, 54194, 13251, 8441986, 12291, 8442530, 12931,
    8438412, 4194304, 50060, 49548, 8405483, 8422247, 77955, 8704686, 144268, 8966308, 196812,
    9175352, 4261903, 8439436]
    ![9815181, 9815566, 1323563, 1323559, 13267, 672, 8451983, 512, 8451791, 128, 1024,
    1325231, 9819276, 9823756, 9745731, 9729987, 66176, 8570816, 1114156, 12000313, 327724,
    2091066, 5517487, 8389248] he hxi hf (by decide +kernel)
  have hc3 : monsterCo1GeometryVectorPoint148AfterInverseMatrix *
    monsterCo1GeometryVectorPoint109Matrix = monsterCo1GeometryVectorPoint148Matrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![9815181, 9815566, 1323563, 1323559, 13267, 672, 8451983, 512, 8451791, 128, 1024,
    1325231, 9819276, 9823756, 9745731, 9729987, 66176, 8570816, 1114156, 12000313, 327724,
    2091066, 5517487, 8389248]
    ![57552, 13349553, 7074506, 8123082, 1152, 8446145, 81, 8445969, 8390364, 1106439, 8388768,
    2566332, 13538546, 1191, 2131900, 10520538, 11279478, 3462808, 11673201, 13246712, 8414912,
    10512106, 1412614, 1137]
    ![942257, 5583046, 14437001, 13388425, 1425967, 1106647, 377417, 1106439, 8766660, 8445969,
    8388768, 37609, 12588179, 10389200, 9912067, 8863091, 3939936, 2414260, 12360311, 10001009,
    9364166, 16194272, 3290195, 9438823] hf hy hc (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_line_products
    monsterCo1GeometryVectorPoint13Transport monsterCo1GeometryVectorPoint109Transport 5
    monsterCo1GeometryVectorPoint13Matrix monsterCo1GeometryVectorPoint13InverseMatrix
    monsterCo1GeometryVectorPoint109Matrix
    monsterCo1GeometryVectorPoint148AfterSignMatrix
    monsterCo1GeometryVectorPoint148AfterInverseMatrix monsterCo1GeometryVectorPoint148Matrix
    monsterCo1GeometryVectorPoint13Transport_binary
    monsterCo1GeometryVectorPoint13Transport_inverse_binary
    monsterCo1GeometryVectorPoint109Transport_binary
    hc1 hc2 hc3 v

/-- Source point 148 is the literal actual transported frame point. -/
def monsterCo1GeometryVectorPoint148 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryVectorPoint148Transport • monsterCo1GeometryBasePoint

/-- Complete binary coordinates of this literal actual source point. -/
theorem monsterCo1GeometryVectorPoint148_binary :
    monsterCo1GeometryVectorPoint148.val =
      ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 0] := by
  change co1BinaryAction monsterCo1GeometryVectorPoint148Transport monsterCo1GeometryBasePoint.val =
      _
  rw [monsterCo1GeometryVectorPoint148Transport_binary, monsterCo1GeometryBasePoint_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
