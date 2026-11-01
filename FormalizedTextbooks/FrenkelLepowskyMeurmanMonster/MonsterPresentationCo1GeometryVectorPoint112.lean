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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint036
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint065

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The literal actual two-core word for source point 112. -/
def monsterCo1GeometryVectorPoint112Transport : Co1 :=
  monsterCo1GeometryVectorPoint36Transport * monsterCo1GeometryTransportOperator 3 *
    monsterCo1GeometryVectorPoint36Transport⁻¹ * monsterCo1GeometryVectorPoint65Transport

/-- Complete displayed binary matrix of actual transport 112. -/
def monsterCo1GeometryVectorPoint112Matrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![10355176, 10393032, 2593230, 10973582, 12157072, 3736352, 12125990, 12158022, 7281675,
      7305563, 10355080, 113124, 8778824, 951490, 5292238, 14566509, 11600246, 6765435,
      1080196, 5653348, 3179696, 3205014, 12383247, 26400]

/-- First complete finite matrix product in literal actual transport 112. -/
def monsterCo1GeometryVectorPoint112AfterSignMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![8446976, 5120, 8394496, 8393984, 8389648, 8389680, 8389824, 8389696, 24784, 8430704,
      58368, 4530937, 13671679, 9437393, 10536000, 11584560, 8622618, 8542070, 554634, 831926,
      1754, 8390262, 13670609, 8389632]

/-- Second complete finite matrix product in literal actual transport 112. -/
def monsterCo1GeometryVectorPoint112AfterInverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![1, 8388610, 8388612, 8388616, 16, 32, 64, 128, 8388864, 512, 1024, 1107968, 5632, 8352,
      16496, 32976, 65708, 131286, 262316, 524410, 1048576, 2098177, 4194817, 8388608]

set_option maxHeartbeats 24000000 in
-- Check every entry of this finite actual transport matrix in the Lean kernel.
/-- Every column of transport 112 is its actual Conway binary action. -/
theorem monsterCo1GeometryVectorPoint112Transport_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint112Transport v =
      monsterCo1GeometryVectorPoint112Matrix *ᵥ v := by
  have hx : monsterCo1GeometryVectorPoint36Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![8446976, 8392704, 4864, 4352, 8389648, 8389680, 8389824, 8389696, 8414416, 8430704,
    58368, 12919938, 5299343, 9437345, 2146464, 3195040, 8622186, 8540390, 554234, 832598,
    1754, 1654, 13686945, 8389632] := by decide +kernel
  have hxi : monsterCo1GeometryVectorPoint36InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![58609, 15732928, 5248109, 6296733, 8388624, 48, 8388736, 192, 1035, 12, 8389633,
    12532786, 1027, 8389617, 673, 337, 3343296, 2229886, 3933168, 9700719, 49152, 17152,
    16718785, 1025] := by decide +kernel
  have hy : monsterCo1GeometryVectorPoint65Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![10355176, 10416872, 2619118, 10950318, 12157072, 3736352, 12125990, 12158022, 7306027,
    7305563, 10355080, 11615541, 7638171, 9307044, 6898776, 6768541, 11626064, 6765709,
    1055906, 5645236, 3179696, 3205110, 5082300, 26400] := by decide +kernel
  have he : monsterCo1GeometryVectorPoint112AfterSignMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![8446976, 5120, 8394496, 8393984, 8389648, 8389680, 8389824, 8389696, 24784, 8430704,
    58368, 4530937, 13671679, 9437393, 10536000, 11584560, 8622618, 8542070, 554634, 831926,
    1754, 8390262, 13670609, 8389632] := by rfl
  have hf : monsterCo1GeometryVectorPoint112AfterInverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![1, 8388610, 8388612, 8388616, 16, 32, 64, 128, 8388864, 512, 1024, 1107968, 5632, 8352,
    16496, 32976, 65708, 131286, 262316, 524410, 1048576, 2098177, 4194817, 8388608] := by rfl
  have hc : monsterCo1GeometryVectorPoint112Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![10355176, 10393032, 2593230, 10973582, 12157072, 3736352, 12125990, 12158022, 7281675,
    7305563, 10355080, 113124, 8778824, 951490, 5292238, 14566509, 11600246, 6765435, 1080196,
    5653348, 3179696, 3205014, 12383247, 26400] := by rfl
  have hc1 : monsterCo1GeometryVectorPoint36Matrix *
    monsterCo1GeometryTransportOperatorMatrix 3 =
    monsterCo1GeometryVectorPoint112AfterSignMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![8446976, 8392704, 4864, 4352, 8389648, 8389680, 8389824, 8389696, 8414416, 8430704,
    58368, 12919938, 5299343, 9437345, 2146464, 3195040, 8622186, 8540390, 554234, 832598,
    1754, 1654, 13686945, 8389632]
      (monsterCo1GeometryBinaryOperatorMasks 3)
    ![8446976, 5120, 8394496, 8393984, 8389648, 8389680, 8389824, 8389696, 24784, 8430704,
    58368, 4530937, 13671679, 9437393, 10536000, 11584560, 8622618, 8542070, 554634, 831926,
    1754, 8390262, 13670609, 8389632] hx (monsterCo1GeometryBinaryOperatorMasks_decode 3) he
    (by decide +kernel)
  have hc2 : monsterCo1GeometryVectorPoint112AfterSignMatrix *
    monsterCo1GeometryVectorPoint36InverseMatrix =
    monsterCo1GeometryVectorPoint112AfterInverseMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![8446976, 5120, 8394496, 8393984, 8389648, 8389680, 8389824, 8389696, 24784, 8430704,
    58368, 4530937, 13671679, 9437393, 10536000, 11584560, 8622618, 8542070, 554634, 831926,
    1754, 8390262, 13670609, 8389632]
    ![58609, 15732928, 5248109, 6296733, 8388624, 48, 8388736, 192, 1035, 12, 8389633,
    12532786, 1027, 8389617, 673, 337, 3343296, 2229886, 3933168, 9700719, 49152, 17152,
    16718785, 1025]
    ![1, 8388610, 8388612, 8388616, 16, 32, 64, 128, 8388864, 512, 1024, 1107968, 5632, 8352,
    16496, 32976, 65708, 131286, 262316, 524410, 1048576, 2098177, 4194817, 8388608] he hxi hf
    (by decide +kernel)
  have hc3 : monsterCo1GeometryVectorPoint112AfterInverseMatrix *
    monsterCo1GeometryVectorPoint65Matrix = monsterCo1GeometryVectorPoint112Matrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![1, 8388610, 8388612, 8388616, 16, 32, 64, 128, 8388864, 512, 1024, 1107968, 5632, 8352,
    16496, 32976, 65708, 131286, 262316, 524410, 1048576, 2098177, 4194817, 8388608]
    ![10355176, 10416872, 2619118, 10950318, 12157072, 3736352, 12125990, 12158022, 7306027,
    7305563, 10355080, 11615541, 7638171, 9307044, 6898776, 6768541, 11626064, 6765709,
    1055906, 5645236, 3179696, 3205110, 5082300, 26400]
    ![10355176, 10393032, 2593230, 10973582, 12157072, 3736352, 12125990, 12158022, 7281675,
    7305563, 10355080, 113124, 8778824, 951490, 5292238, 14566509, 11600246, 6765435, 1080196,
    5653348, 3179696, 3205014, 12383247, 26400] hf hy hc (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_line_products
    monsterCo1GeometryVectorPoint36Transport monsterCo1GeometryVectorPoint65Transport 3
    monsterCo1GeometryVectorPoint36Matrix monsterCo1GeometryVectorPoint36InverseMatrix
    monsterCo1GeometryVectorPoint65Matrix
    monsterCo1GeometryVectorPoint112AfterSignMatrix
    monsterCo1GeometryVectorPoint112AfterInverseMatrix monsterCo1GeometryVectorPoint112Matrix
    monsterCo1GeometryVectorPoint36Transport_binary
    monsterCo1GeometryVectorPoint36Transport_inverse_binary
    monsterCo1GeometryVectorPoint65Transport_binary
    hc1 hc2 hc3 v

/-- Source point 112 is the literal actual transported frame point. -/
def monsterCo1GeometryVectorPoint112 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryVectorPoint112Transport • monsterCo1GeometryBasePoint

/-- Complete binary coordinates of this literal actual source point. -/
theorem monsterCo1GeometryVectorPoint112_binary :
    monsterCo1GeometryVectorPoint112.val =
      ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0] := by
  change co1BinaryAction monsterCo1GeometryVectorPoint112Transport monsterCo1GeometryBasePoint.val =
      _
  rw [monsterCo1GeometryVectorPoint112Transport_binary, monsterCo1GeometryBasePoint_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
