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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint057
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint089

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The literal actual two-core word for source point 140. -/
def monsterCo1GeometryVectorPoint140Transport : Co1 :=
  monsterCo1GeometryVectorPoint57Transport * monsterCo1GeometryTransportOperator 1 *
    monsterCo1GeometryVectorPoint57Transport⁻¹ * monsterCo1GeometryVectorPoint89Transport

/-- Complete displayed binary matrix of actual transport 140. -/
def monsterCo1GeometryVectorPoint140Matrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![49152, 1082881, 11577329, 10528081, 5286479, 5286462, 5270223, 5270046, 12635279,
      12635182, 9495040, 5300909, 951510, 1425580, 2477229, 3525805, 6845694, 7574623, 8172638,
      6444287, 79500, 316972, 1435808, 58368]

/-- First complete finite matrix product in literal actual transport 140. -/
def monsterCo1GeometryVectorPoint140AfterSignMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![8389649, 8902163, 11007033, 2617950, 57504, 8445984, 57456, 57584, 26272, 25408, 8388784,
      14099577, 8401744, 1552, 8397888, 8398400, 13744293, 12942826, 5201178, 6003197, 1106957,
      9495553, 12910940, 1200]

/-- Second complete finite matrix product in literal actual transport 140. -/
def monsterCo1GeometryVectorPoint140AfterInverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![241, 1218, 852, 936, 8389648, 8389664, 8389696, 8389760, 256, 512, 1024, 985869, 8393728,
      8192, 8406016, 8422400, 86944, 168784, 291744, 570192, 9487600, 10536176, 5186317,
      8388608]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 24000000 in
-- Check every entry of this finite actual transport matrix in the Lean kernel.
/-- Every column of transport 140 is its actual Conway binary action. -/
theorem monsterCo1GeometryVectorPoint140Transport_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint140Transport v =
      monsterCo1GeometryVectorPoint140Matrix *ᵥ v := by
  have hx : monsterCo1GeometryVectorPoint57Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![1041, 513571, 11006217, 11007854, 8447136, 58400, 8447088, 8447216, 26272, 25408,
    8388784, 14099015, 14160, 1552, 8256, 8768, 5352069, 12938698, 13584682, 6000589, 1106445,
    9495041, 12910962, 1200] := by decide +kernel
  have hxi : monsterCo1GeometryVectorPoint57InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![57345, 12567357, 4186976, 1041296, 8447216, 8446144, 8447072, 192, 8389520, 49152,
    8389872, 13485664, 8418192, 8430688, 8421776, 49632, 4987907, 6270016, 11306157, 5834928,
    2147553, 11576219, 2078883, 240] := by decide +kernel
  have hy : monsterCo1GeometryVectorPoint89Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![49312, 8414416, 11560912, 10511824, 12627023, 12627006, 12610767, 12610590, 12635279,
    12635182, 9495040, 4530348, 10388182, 1425580, 11913901, 10865325, 4455428, 4725765,
    4389896, 4987913, 8466476, 8704140, 1436173, 58368] := by rfl
  have he : monsterCo1GeometryVectorPoint140AfterSignMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![8389649, 8902163, 11007033, 2617950, 57504, 8445984, 57456, 57584, 26272, 25408, 8388784,
    14099577, 8401744, 1552, 8397888, 8398400, 13744293, 12942826, 5201178, 6003197, 1106957,
    9495553, 12910940, 1200] := by rfl
  have hf : monsterCo1GeometryVectorPoint140AfterInverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![241, 1218, 852, 936, 8389648, 8389664, 8389696, 8389760, 256, 512, 1024, 985869, 8393728,
    8192, 8406016, 8422400, 86944, 168784, 291744, 570192, 9487600, 10536176, 5186317, 8388608]
    := by rfl
  have hc : monsterCo1GeometryVectorPoint140Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![49152, 1082881, 11577329, 10528081, 5286479, 5286462, 5270223, 5270046, 12635279,
    12635182, 9495040, 5300909, 951510, 1425580, 2477229, 3525805, 6845694, 7574623, 8172638,
    6444287, 79500, 316972, 1435808, 58368] := by rfl
  have hc1 : monsterCo1GeometryVectorPoint57Matrix *
    monsterCo1GeometryTransportOperatorMatrix 1 =
    monsterCo1GeometryVectorPoint140AfterSignMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![1041, 513571, 11006217, 11007854, 8447136, 58400, 8447088, 8447216, 26272, 25408,
    8388784, 14099015, 14160, 1552, 8256, 8768, 5352069, 12938698, 13584682, 6000589, 1106445,
    9495041, 12910962, 1200]
      (monsterCo1GeometryBinaryOperatorMasks 1)
    ![8389649, 8902163, 11007033, 2617950, 57504, 8445984, 57456, 57584, 26272, 25408, 8388784,
    14099577, 8401744, 1552, 8397888, 8398400, 13744293, 12942826, 5201178, 6003197, 1106957,
    9495553, 12910940, 1200] hx (monsterCo1GeometryBinaryOperatorMasks_decode 1) he
      (by decide +kernel)
  have hc2 : monsterCo1GeometryVectorPoint140AfterSignMatrix *
    monsterCo1GeometryVectorPoint57InverseMatrix =
    monsterCo1GeometryVectorPoint140AfterInverseMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![8389649, 8902163, 11007033, 2617950, 57504, 8445984, 57456, 57584, 26272, 25408, 8388784,
    14099577, 8401744, 1552, 8397888, 8398400, 13744293, 12942826, 5201178, 6003197, 1106957,
    9495553, 12910940, 1200]
    ![57345, 12567357, 4186976, 1041296, 8447216, 8446144, 8447072, 192, 8389520, 49152,
    8389872, 13485664, 8418192, 8430688, 8421776, 49632, 4987907, 6270016, 11306157, 5834928,
    2147553, 11576219, 2078883, 240]
    ![241, 1218, 852, 936, 8389648, 8389664, 8389696, 8389760, 256, 512, 1024, 985869, 8393728,
    8192, 8406016, 8422400, 86944, 168784, 291744, 570192, 9487600, 10536176, 5186317, 8388608]
    he hxi hf (by decide +kernel)
  have hc3 : monsterCo1GeometryVectorPoint140AfterInverseMatrix *
    monsterCo1GeometryVectorPoint89Matrix = monsterCo1GeometryVectorPoint140Matrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![241, 1218, 852, 936, 8389648, 8389664, 8389696, 8389760, 256, 512, 1024, 985869, 8393728,
    8192, 8406016, 8422400, 86944, 168784, 291744, 570192, 9487600, 10536176, 5186317, 8388608]
    ![49312, 8414416, 11560912, 10511824, 12627023, 12627006, 12610767, 12610590, 12635279,
    12635182, 9495040, 4530348, 10388182, 1425580, 11913901, 10865325, 4455428, 4725765,
    4389896, 4987913, 8466476, 8704140, 1436173, 58368]
    ![49152, 1082881, 11577329, 10528081, 5286479, 5286462, 5270223, 5270046, 12635279,
    12635182, 9495040, 5300909, 951510, 1425580, 2477229, 3525805, 6845694, 7574623, 8172638,
    6444287, 79500, 316972, 1435808, 58368] hf hy hc (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_line_products
    monsterCo1GeometryVectorPoint57Transport monsterCo1GeometryVectorPoint89Transport 1
    monsterCo1GeometryVectorPoint57Matrix monsterCo1GeometryVectorPoint57InverseMatrix
    monsterCo1GeometryVectorPoint89Matrix
    monsterCo1GeometryVectorPoint140AfterSignMatrix
    monsterCo1GeometryVectorPoint140AfterInverseMatrix monsterCo1GeometryVectorPoint140Matrix
    monsterCo1GeometryVectorPoint57Transport_binary
    monsterCo1GeometryVectorPoint57Transport_inverse_binary
    monsterCo1GeometryVectorPoint89Transport_binary
    hc1 hc2 hc3 v

/-- The displayed inverse matrix of actual source transport 140. -/
def monsterCo1GeometryVectorPoint140InverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![1008, 13618512, 16522910, 15990383, 1326, 161, 1615, 81, 13591658, 49404, 12517616,
      7389184, 9822380, 4129009, 12518399, 12518398, 704753, 10634910, 377073, 9717151, 49152,
      13591296, 3206141, 4129804]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 24000000 in
-- Check all entries of the right inverse before applying actual action injectivity.
/-- The inverse matrix is the inverse of the literal actual Conway transport. -/
theorem monsterCo1GeometryVectorPoint140Transport_inverse_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint140Transport⁻¹ v =
      monsterCo1GeometryVectorPoint140InverseMatrix *ᵥ v := by
  have hm : monsterCo1GeometryVectorPoint140Matrix = monsterCo1GeometryBinaryMaskMatrix
      ![49152, 1082881, 11577329, 10528081, 5286479, 5286462, 5270223, 5270046, 12635279,
        12635182, 9495040, 5300909, 951510, 1425580, 2477229, 3525805, 6845694, 7574623,
        8172638, 6444287, 79500, 316972, 1435808, 58368] := by rfl
  have hmi : monsterCo1GeometryVectorPoint140InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
      ![1008, 13618512, 16522910, 15990383, 1326, 161, 1615, 81, 13591658, 49404, 12517616,
        7389184, 9822380, 4129009, 12518399, 12518398, 704753, 10634910, 377073, 9717151,
        49152, 13591296, 3206141, 4129804] := by rfl
  have hi : (1 : Matrix (Fin 24) (Fin 24) (ZMod 2)) = monsterCo1GeometryBinaryMaskMatrix
      ![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536,
        131072, 262144, 524288, 1048576, 2097152, 4194304, 8388608] := by decide +kernel
  have hc : monsterCo1GeometryVectorPoint140Matrix *
    monsterCo1GeometryVectorPoint140InverseMatrix = 1 :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
      ![49152, 1082881, 11577329, 10528081, 5286479, 5286462, 5270223, 5270046, 12635279,
        12635182, 9495040, 5300909, 951510, 1425580, 2477229, 3525805, 6845694, 7574623,
        8172638, 6444287, 79500, 316972, 1435808, 58368]
      ![1008, 13618512, 16522910, 15990383, 1326, 161, 1615, 81, 13591658, 49404, 12517616,
        7389184, 9822380, 4129009, 12518399, 12518398, 704753, 10634910, 377073, 9717151,
        49152, 13591296, 3206141, 4129804]
      ![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536,
        131072, 262144, 524288, 1048576, 2097152, 4194304, 8388608] hm hmi hi
      (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_inv monsterCo1GeometryVectorPoint140Transport _ _
    monsterCo1GeometryVectorPoint140Transport_binary hc v

/-- Source point 140 is the literal actual transported frame point. -/
def monsterCo1GeometryVectorPoint140 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryVectorPoint140Transport • monsterCo1GeometryBasePoint

/-- Complete binary coordinates of this literal actual source point. -/
theorem monsterCo1GeometryVectorPoint140_binary :
    monsterCo1GeometryVectorPoint140.val =
      ![0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0] := by
  change co1BinaryAction monsterCo1GeometryVectorPoint140Transport monsterCo1GeometryBasePoint.val =
      _
  rw [monsterCo1GeometryVectorPoint140Transport_binary, monsterCo1GeometryBasePoint_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
