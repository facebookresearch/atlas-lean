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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint035
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint068

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The literal actual two-core word for source point 114. -/
def monsterCo1GeometryVectorPoint114Transport : Co1 :=
  monsterCo1GeometryVectorPoint35Transport * monsterCo1GeometryTransportOperator 6 *
    monsterCo1GeometryVectorPoint35Transport⁻¹ * monsterCo1GeometryVectorPoint68Transport

/-- Complete displayed binary matrix of actual transport 114. -/
def monsterCo1GeometryVectorPoint114Matrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![8447009, 10747289, 220756, 253923, 58384, 58545, 8388849, 57521, 1097990, 49980, 8388768,
      10270896, 11951280, 8430762, 10494567, 10519181, 477755, 4336324, 465502, 13592331,
      50828, 3145754, 1209035, 57393]

/-- First complete finite matrix product in literal actual transport 114. -/
def monsterCo1GeometryVectorPoint114AfterSignMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![8388609, 12721168, 15923339, 14874701, 16, 8388656, 192, 64, 25104, 8430576, 8389632,
      5380824, 13766342, 9496279, 10487116, 11536266, 238533, 156166, 8954614, 811024, 8388730,
      214, 196096, 57360]

/-- Second complete finite matrix product in literal actual transport 114. -/
def monsterCo1GeometryVectorPoint114AfterInverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![1, 2280785, 11675942, 9578810, 16, 8447009, 64, 128, 49484, 26310, 1024, 181571, 8534354,
      10535937, 3162224, 1081440, 108741, 180300, 11805757, 2621456, 9495553, 2097152,
      14821698, 58385]

set_option maxHeartbeats 24000000 in
-- Check every entry of this finite actual transport matrix in the Lean kernel.
/-- Every column of transport 114 is its actual Conway binary action. -/
theorem monsterCo1GeometryVectorPoint114Transport_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint114Transport v =
      monsterCo1GeometryVectorPoint114Matrix *ᵥ v := by
  have hx : monsterCo1GeometryVectorPoint35Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![8388609, 4201487, 15792142, 14743566, 16, 48, 192, 64, 24784, 41072, 8389632, 13638145,
    13635087, 1107457, 10487040, 11536128, 237642, 155846, 565370, 811222, 122, 214, 65039,
    8445952] := by decide +kernel
  have hxi : monsterCo1GeometryVectorPoint35InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![8446976, 3198194, 1100962, 2149458, 16, 48, 128, 192, 8405003, 49164, 8445953, 12638221,
    8401923, 59377, 59041, 58705, 3343296, 2228544, 3933168, 1311392, 12, 8389643, 4203535,
    8446977] := by decide +kernel
  have hy : monsterCo1GeometryVectorPoint68Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![8447009, 8319970, 14587395, 15659966, 58384, 8447041, 8388849, 57521, 9494698, 8390364,
    8388768, 7426753, 14373409, 3187776, 1107105, 2138177, 12095129, 12716904, 12058052,
    16745217, 8439420, 3145754, 5216336, 8389841] := by decide +kernel
  have he : monsterCo1GeometryVectorPoint114AfterSignMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![8388609, 12721168, 15923339, 14874701, 16, 8388656, 192, 64, 25104, 8430576, 8389632,
    5380824, 13766342, 9496279, 10487116, 11536266, 238533, 156166, 8954614, 811024, 8388730,
    214, 196096, 57360] := by rfl
  have hf : monsterCo1GeometryVectorPoint114AfterInverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![1, 2280785, 11675942, 9578810, 16, 8447009, 64, 128, 49484, 26310, 1024, 181571, 8534354,
    10535937, 3162224, 1081440, 108741, 180300, 11805757, 2621456, 9495553, 2097152, 14821698,
    58385] := by rfl
  have hc : monsterCo1GeometryVectorPoint114Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![8447009, 10747289, 220756, 253923, 58384, 58545, 8388849, 57521, 1097990, 49980, 8388768,
    10270896, 11951280, 8430762, 10494567, 10519181, 477755, 4336324, 465502, 13592331, 50828,
    3145754, 1209035, 57393] := by rfl
  have hc1 : monsterCo1GeometryVectorPoint35Matrix *
    monsterCo1GeometryTransportOperatorMatrix 6 =
    monsterCo1GeometryVectorPoint114AfterSignMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![8388609, 4201487, 15792142, 14743566, 16, 48, 192, 64, 24784, 41072, 8389632, 13638145,
    13635087, 1107457, 10487040, 11536128, 237642, 155846, 565370, 811222, 122, 214, 65039,
    8445952]
      (monsterCo1GeometryBinaryOperatorMasks 6)
    ![8388609, 12721168, 15923339, 14874701, 16, 8388656, 192, 64, 25104, 8430576, 8389632,
    5380824, 13766342, 9496279, 10487116, 11536266, 238533, 156166, 8954614, 811024, 8388730,
    214, 196096, 57360] hx (monsterCo1GeometryBinaryOperatorMasks_decode 6) he
      (by decide +kernel)
  have hc2 : monsterCo1GeometryVectorPoint114AfterSignMatrix *
    monsterCo1GeometryVectorPoint35InverseMatrix =
    monsterCo1GeometryVectorPoint114AfterInverseMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![8388609, 12721168, 15923339, 14874701, 16, 8388656, 192, 64, 25104, 8430576, 8389632,
    5380824, 13766342, 9496279, 10487116, 11536266, 238533, 156166, 8954614, 811024, 8388730,
    214, 196096, 57360]
    ![8446976, 3198194, 1100962, 2149458, 16, 48, 128, 192, 8405003, 49164, 8445953, 12638221,
    8401923, 59377, 59041, 58705, 3343296, 2228544, 3933168, 1311392, 12, 8389643, 4203535,
    8446977]
    ![1, 2280785, 11675942, 9578810, 16, 8447009, 64, 128, 49484, 26310, 1024, 181571, 8534354,
    10535937, 3162224, 1081440, 108741, 180300, 11805757, 2621456, 9495553, 2097152, 14821698,
    58385] he hxi hf (by decide +kernel)
  have hc3 : monsterCo1GeometryVectorPoint114AfterInverseMatrix *
    monsterCo1GeometryVectorPoint68Matrix = monsterCo1GeometryVectorPoint114Matrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![1, 2280785, 11675942, 9578810, 16, 8447009, 64, 128, 49484, 26310, 1024, 181571, 8534354,
    10535937, 3162224, 1081440, 108741, 180300, 11805757, 2621456, 9495553, 2097152, 14821698,
    58385]
    ![8447009, 8319970, 14587395, 15659966, 58384, 8447041, 8388849, 57521, 9494698, 8390364,
    8388768, 7426753, 14373409, 3187776, 1107105, 2138177, 12095129, 12716904, 12058052,
    16745217, 8439420, 3145754, 5216336, 8389841]
    ![8447009, 10747289, 220756, 253923, 58384, 58545, 8388849, 57521, 1097990, 49980, 8388768,
    10270896, 11951280, 8430762, 10494567, 10519181, 477755, 4336324, 465502, 13592331, 50828,
    3145754, 1209035, 57393] hf hy hc (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_line_products
    monsterCo1GeometryVectorPoint35Transport monsterCo1GeometryVectorPoint68Transport 6
    monsterCo1GeometryVectorPoint35Matrix monsterCo1GeometryVectorPoint35InverseMatrix
    monsterCo1GeometryVectorPoint68Matrix
    monsterCo1GeometryVectorPoint114AfterSignMatrix
    monsterCo1GeometryVectorPoint114AfterInverseMatrix monsterCo1GeometryVectorPoint114Matrix
    monsterCo1GeometryVectorPoint35Transport_binary
    monsterCo1GeometryVectorPoint35Transport_inverse_binary
    monsterCo1GeometryVectorPoint68Transport_binary
    hc1 hc2 hc3 v

/-- Source point 114 is the literal actual transported frame point. -/
def monsterCo1GeometryVectorPoint114 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryVectorPoint114Transport • monsterCo1GeometryBasePoint

/-- Complete binary coordinates of this literal actual source point. -/
theorem monsterCo1GeometryVectorPoint114_binary :
    monsterCo1GeometryVectorPoint114.val =
      ![0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0] := by
  change co1BinaryAction monsterCo1GeometryVectorPoint114Transport monsterCo1GeometryBasePoint.val =
      _
  rw [monsterCo1GeometryVectorPoint114Transport_binary, monsterCo1GeometryBasePoint_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
