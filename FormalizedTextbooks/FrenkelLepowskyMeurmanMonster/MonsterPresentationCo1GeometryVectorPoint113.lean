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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint065

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The literal actual two-core word for source point 113. -/
def monsterCo1GeometryVectorPoint113Transport : Co1 :=
  monsterCo1GeometryVectorPoint57Transport * monsterCo1GeometryTransportOperator 1 *
    monsterCo1GeometryVectorPoint57Transport⁻¹ * monsterCo1GeometryVectorPoint65Transport

/-- Complete displayed binary matrix of actual transport 113. -/
def monsterCo1GeometryVectorPoint113Matrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![1966392, 28672, 2585384, 2593720, 2614840, 10970504, 2580878, 2613998, 7306027, 7305563,
      10355080, 4176678, 15395379, 9307044, 16196336, 16326965, 2894725, 7631437, 217811,
      13332176, 2154765, 2130507, 5048587, 26400]

/-- First complete finite matrix product in literal actual transport 113. -/
def monsterCo1GeometryVectorPoint113AfterSignMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![8389649, 8902163, 11007033, 2617950, 57504, 8445984, 57456, 57584, 26272, 25408, 8388784,
      14099577, 8401744, 1552, 8397888, 8398400, 13744293, 12942826, 5201178, 6003197, 1106957,
      9495553, 12910940, 1200]

/-- Second complete finite matrix product in literal actual transport 113. -/
def monsterCo1GeometryVectorPoint113AfterInverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![241, 1218, 852, 936, 8389648, 8389664, 8389696, 8389760, 256, 512, 1024, 985869, 8393728,
      8192, 8406016, 8422400, 86944, 168784, 291744, 570192, 9487600, 10536176, 5186317,
      8388608]

set_option maxHeartbeats 24000000 in
-- Check every entry of this finite actual transport matrix in the Lean kernel.
/-- Every column of transport 113 is its actual Conway binary action. -/
theorem monsterCo1GeometryVectorPoint113Transport_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint113Transport v =
      monsterCo1GeometryVectorPoint113Matrix *ᵥ v := by
  have hx : monsterCo1GeometryVectorPoint57Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![1041, 513571, 11006217, 11007854, 8447136, 58400, 8447088, 8447216, 26272, 25408,
    8388784, 14099015, 14160, 1552, 8256, 8768, 5352069, 12938698, 13584682, 6000589, 1106445,
    9495041, 12910962, 1200] := by decide +kernel
  have hxi : monsterCo1GeometryVectorPoint57InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![57345, 12567357, 4186976, 1041296, 8447216, 8446144, 8447072, 192, 8389520, 49152,
    8389872, 13485664, 8418192, 8430688, 8421776, 49632, 4987907, 6270016, 11306157, 5834928,
    2147553, 11576219, 2078883, 240] := by decide +kernel
  have hy : monsterCo1GeometryVectorPoint65Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![10355176, 10416872, 2619118, 10950318, 12157072, 3736352, 12125990, 12158022, 7306027,
    7305563, 10355080, 11615541, 7638171, 9307044, 6898776, 6768541, 11626064, 6765709,
    1055906, 5645236, 3179696, 3205110, 5082300, 26400] := by decide +kernel
  have he : monsterCo1GeometryVectorPoint113AfterSignMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![8389649, 8902163, 11007033, 2617950, 57504, 8445984, 57456, 57584, 26272, 25408, 8388784,
    14099577, 8401744, 1552, 8397888, 8398400, 13744293, 12942826, 5201178, 6003197, 1106957,
    9495553, 12910940, 1200] := by rfl
  have hf : monsterCo1GeometryVectorPoint113AfterInverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![241, 1218, 852, 936, 8389648, 8389664, 8389696, 8389760, 256, 512, 1024, 985869, 8393728,
    8192, 8406016, 8422400, 86944, 168784, 291744, 570192, 9487600, 10536176, 5186317, 8388608]
    := by rfl
  have hc : monsterCo1GeometryVectorPoint113Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![1966392, 28672, 2585384, 2593720, 2614840, 10970504, 2580878, 2613998, 7306027, 7305563,
    10355080, 4176678, 15395379, 9307044, 16196336, 16326965, 2894725, 7631437, 217811,
    13332176, 2154765, 2130507, 5048587, 26400] := by rfl
  have hc1 : monsterCo1GeometryVectorPoint57Matrix *
    monsterCo1GeometryTransportOperatorMatrix 1 =
    monsterCo1GeometryVectorPoint113AfterSignMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![1041, 513571, 11006217, 11007854, 8447136, 58400, 8447088, 8447216, 26272, 25408,
    8388784, 14099015, 14160, 1552, 8256, 8768, 5352069, 12938698, 13584682, 6000589, 1106445,
    9495041, 12910962, 1200]
      (monsterCo1GeometryBinaryOperatorMasks 1)
    ![8389649, 8902163, 11007033, 2617950, 57504, 8445984, 57456, 57584, 26272, 25408, 8388784,
    14099577, 8401744, 1552, 8397888, 8398400, 13744293, 12942826, 5201178, 6003197, 1106957,
    9495553, 12910940, 1200] hx (monsterCo1GeometryBinaryOperatorMasks_decode 1) he
      (by decide +kernel)
  have hc2 : monsterCo1GeometryVectorPoint113AfterSignMatrix *
    monsterCo1GeometryVectorPoint57InverseMatrix =
    monsterCo1GeometryVectorPoint113AfterInverseMatrix :=
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
  have hc3 : monsterCo1GeometryVectorPoint113AfterInverseMatrix *
    monsterCo1GeometryVectorPoint65Matrix = monsterCo1GeometryVectorPoint113Matrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![241, 1218, 852, 936, 8389648, 8389664, 8389696, 8389760, 256, 512, 1024, 985869, 8393728,
    8192, 8406016, 8422400, 86944, 168784, 291744, 570192, 9487600, 10536176, 5186317, 8388608]
    ![10355176, 10416872, 2619118, 10950318, 12157072, 3736352, 12125990, 12158022, 7306027,
    7305563, 10355080, 11615541, 7638171, 9307044, 6898776, 6768541, 11626064, 6765709,
    1055906, 5645236, 3179696, 3205110, 5082300, 26400]
    ![1966392, 28672, 2585384, 2593720, 2614840, 10970504, 2580878, 2613998, 7306027, 7305563,
    10355080, 4176678, 15395379, 9307044, 16196336, 16326965, 2894725, 7631437, 217811,
    13332176, 2154765, 2130507, 5048587, 26400] hf hy hc (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_line_products
    monsterCo1GeometryVectorPoint57Transport monsterCo1GeometryVectorPoint65Transport 1
    monsterCo1GeometryVectorPoint57Matrix monsterCo1GeometryVectorPoint57InverseMatrix
    monsterCo1GeometryVectorPoint65Matrix
    monsterCo1GeometryVectorPoint113AfterSignMatrix
    monsterCo1GeometryVectorPoint113AfterInverseMatrix monsterCo1GeometryVectorPoint113Matrix
    monsterCo1GeometryVectorPoint57Transport_binary
    monsterCo1GeometryVectorPoint57Transport_inverse_binary
    monsterCo1GeometryVectorPoint65Transport_binary
    hc1 hc2 hc3 v

/-- Source point 113 is the literal actual transported frame point. -/
def monsterCo1GeometryVectorPoint113 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryVectorPoint113Transport • monsterCo1GeometryBasePoint

/-- Complete binary coordinates of this literal actual source point. -/
theorem monsterCo1GeometryVectorPoint113_binary :
    monsterCo1GeometryVectorPoint113.val =
      ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0] := by
  change co1BinaryAction monsterCo1GeometryVectorPoint113Transport monsterCo1GeometryBasePoint.val =
      _
  rw [monsterCo1GeometryVectorPoint113Transport_binary, monsterCo1GeometryBasePoint_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
