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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint031
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint035

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The literal actual two-core word for source point 77. -/
def monsterCo1GeometryVectorPoint77Transport : Co1 :=
  monsterCo1GeometryVectorPoint31Transport * monsterCo1GeometryTransportOperator 1 *
    monsterCo1GeometryVectorPoint31Transport⁻¹ * monsterCo1GeometryVectorPoint35Transport

/-- Complete displayed binary matrix of actual transport 77. -/
def monsterCo1GeometryVectorPoint77Matrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![8446081, 10417350, 964497, 1996049, 16, 57520, 58384, 1040, 24784, 26272, 8389632,
      10749659, 9364182, 1049297, 8413398, 9471494, 5716247, 2228544, 2266793, 5417567,
      2115500, 2131328, 2803725, 8389840]

/-- First complete finite matrix product in literal actual transport 77. -/
def monsterCo1GeometryVectorPoint77AfterSignMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![8447184, 10021115, 12086240, 11061712, 8388736, 8447152, 57441, 1057, 8438204, 1099095,
      8388768, 4741749, 1936489, 17627, 11543991, 3171676, 7818775, 3417240, 12702187, 638766,
      2098587, 3147755, 13001836, 58433]

/-- Second complete finite matrix product in literal actual transport 77. -/
def monsterCo1GeometryVectorPoint77AfterInverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![58560, 11195406, 701029, 684373, 16, 58593, 8389648, 8445969, 256, 8397229, 1024,
      2893575, 11190300, 8397904, 10544465, 2105601, 887495, 2246080, 187574, 2234224,
      11567788, 8405392, 12990694, 1104]

set_option maxHeartbeats 24000000 in
-- Check every entry of this finite actual transport matrix in the Lean kernel.
/-- Every column of transport 77 is its actual Conway binary action. -/
theorem monsterCo1GeometryVectorPoint77Transport_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint77Transport v =
      monsterCo1GeometryVectorPoint77Matrix *ᵥ v := by
  have hx : monsterCo1GeometryVectorPoint31Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![57552, 10026741, 12089582, 11065566, 8388736, 57520, 58465, 8389665, 8438204, 9488215,
    8388768, 4738677, 1940039, 16603, 11543223, 3171932, 7821607, 11805592, 4313541, 634624,
    10486939, 11535595, 13001842, 57409] := by decide +kernel
  have hxi : monsterCo1GeometryVectorPoint31InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![57425, 425132, 11992154, 3586241, 209, 1040, 1073, 8446081, 2122301, 49980, 8389712,
    7989028, 11283287, 2148119, 11591773, 1098538, 11711790, 14575124, 10813003, 5501798,
    3145968, 10494125, 11282312, 8446097] := by decide +kernel
  have hy : monsterCo1GeometryVectorPoint35Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![8388609, 4201487, 15792142, 14743566, 16, 48, 192, 64, 24784, 41072, 8389632, 13638145,
    13635087, 1107457, 10487040, 11536128, 237642, 155846, 565370, 811222, 122, 214, 65039,
    8445952] := by decide +kernel
  have he : monsterCo1GeometryVectorPoint77AfterSignMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![8447184, 10021115, 12086240, 11061712, 8388736, 8447152, 57441, 1057, 8438204, 1099095,
    8388768, 4741749, 1936489, 17627, 11543991, 3171676, 7818775, 3417240, 12702187, 638766,
    2098587, 3147755, 13001836, 58433] := by rfl
  have hf : monsterCo1GeometryVectorPoint77AfterInverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![58560, 11195406, 701029, 684373, 16, 58593, 8389648, 8445969, 256, 8397229, 1024,
    2893575, 11190300, 8397904, 10544465, 2105601, 887495, 2246080, 187574, 2234224, 11567788,
    8405392, 12990694, 1104] := by rfl
  have hc : monsterCo1GeometryVectorPoint77Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![8446081, 10417350, 964497, 1996049, 16, 57520, 58384, 1040, 24784, 26272, 8389632,
    10749659, 9364182, 1049297, 8413398, 9471494, 5716247, 2228544, 2266793, 5417567, 2115500,
    2131328, 2803725, 8389840] := by rfl
  have hc1 : monsterCo1GeometryVectorPoint31Matrix *
    monsterCo1GeometryTransportOperatorMatrix 1 =
    monsterCo1GeometryVectorPoint77AfterSignMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![57552, 10026741, 12089582, 11065566, 8388736, 57520, 58465, 8389665, 8438204, 9488215,
    8388768, 4738677, 1940039, 16603, 11543223, 3171932, 7821607, 11805592, 4313541, 634624,
    10486939, 11535595, 13001842, 57409]
      (monsterCo1GeometryBinaryOperatorMasks 1)
    ![8447184, 10021115, 12086240, 11061712, 8388736, 8447152, 57441, 1057, 8438204, 1099095,
    8388768, 4741749, 1936489, 17627, 11543991, 3171676, 7818775, 3417240, 12702187, 638766,
    2098587, 3147755, 13001836, 58433] hx (monsterCo1GeometryBinaryOperatorMasks_decode 1) he
    (by decide +kernel)
  have hc2 : monsterCo1GeometryVectorPoint77AfterSignMatrix *
    monsterCo1GeometryVectorPoint31InverseMatrix =
    monsterCo1GeometryVectorPoint77AfterInverseMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![8447184, 10021115, 12086240, 11061712, 8388736, 8447152, 57441, 1057, 8438204, 1099095,
    8388768, 4741749, 1936489, 17627, 11543991, 3171676, 7818775, 3417240, 12702187, 638766,
    2098587, 3147755, 13001836, 58433]
    ![57425, 425132, 11992154, 3586241, 209, 1040, 1073, 8446081, 2122301, 49980, 8389712,
    7989028, 11283287, 2148119, 11591773, 1098538, 11711790, 14575124, 10813003, 5501798,
    3145968, 10494125, 11282312, 8446097]
    ![58560, 11195406, 701029, 684373, 16, 58593, 8389648, 8445969, 256, 8397229, 1024,
    2893575, 11190300, 8397904, 10544465, 2105601, 887495, 2246080, 187574, 2234224, 11567788,
    8405392, 12990694, 1104] he hxi hf (by decide +kernel)
  have hc3 : monsterCo1GeometryVectorPoint77AfterInverseMatrix *
    monsterCo1GeometryVectorPoint35Matrix = monsterCo1GeometryVectorPoint77Matrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![58560, 11195406, 701029, 684373, 16, 58593, 8389648, 8445969, 256, 8397229, 1024,
    2893575, 11190300, 8397904, 10544465, 2105601, 887495, 2246080, 187574, 2234224, 11567788,
    8405392, 12990694, 1104]
    ![8388609, 4201487, 15792142, 14743566, 16, 48, 192, 64, 24784, 41072, 8389632, 13638145,
    13635087, 1107457, 10487040, 11536128, 237642, 155846, 565370, 811222, 122, 214, 65039,
    8445952]
    ![8446081, 10417350, 964497, 1996049, 16, 57520, 58384, 1040, 24784, 26272, 8389632,
    10749659, 9364182, 1049297, 8413398, 9471494, 5716247, 2228544, 2266793, 5417567, 2115500,
    2131328, 2803725, 8389840] hf hy hc (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_line_products
    monsterCo1GeometryVectorPoint31Transport monsterCo1GeometryVectorPoint35Transport 1
    monsterCo1GeometryVectorPoint31Matrix monsterCo1GeometryVectorPoint31InverseMatrix
    monsterCo1GeometryVectorPoint35Matrix
    monsterCo1GeometryVectorPoint77AfterSignMatrix
    monsterCo1GeometryVectorPoint77AfterInverseMatrix monsterCo1GeometryVectorPoint77Matrix
    monsterCo1GeometryVectorPoint31Transport_binary
    monsterCo1GeometryVectorPoint31Transport_inverse_binary
    monsterCo1GeometryVectorPoint35Transport_binary
    hc1 hc2 hc3 v

/-- The displayed inverse matrix of actual source transport 77. -/
def monsterCo1GeometryVectorPoint77InverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![57424, 3600533, 3585285, 423625, 16, 58609, 8445969, 58369, 41114, 8390496, 144,
      12597261, 8443090, 8396957, 9629, 8390080, 10471575, 2228544, 9447591, 11696967, 49968,
      10502603, 15526728, 1168]

set_option maxHeartbeats 24000000 in
-- Check all entries of the right inverse before applying actual action injectivity.
/-- The inverse matrix is the inverse of the literal actual Conway transport. -/
theorem monsterCo1GeometryVectorPoint77Transport_inverse_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint77Transport⁻¹ v =
      monsterCo1GeometryVectorPoint77InverseMatrix *ᵥ v := by
  have hm : monsterCo1GeometryVectorPoint77Matrix = monsterCo1GeometryBinaryMaskMatrix
      ![8446081, 10417350, 964497, 1996049, 16, 57520, 58384, 1040, 24784, 26272, 8389632,
        10749659, 9364182, 1049297, 8413398, 9471494, 5716247, 2228544, 2266793, 5417567,
        2115500, 2131328, 2803725, 8389840] := by rfl
  have hmi : monsterCo1GeometryVectorPoint77InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
      ![57424, 3600533, 3585285, 423625, 16, 58609, 8445969, 58369, 41114, 8390496, 144,
        12597261, 8443090, 8396957, 9629, 8390080, 10471575, 2228544, 9447591, 11696967, 49968,
        10502603, 15526728, 1168] := by rfl
  have hi : (1 : Matrix (Fin 24) (Fin 24) (ZMod 2)) = monsterCo1GeometryBinaryMaskMatrix
      ![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536,
        131072, 262144, 524288, 1048576, 2097152, 4194304, 8388608] := by decide +kernel
  have hc : monsterCo1GeometryVectorPoint77Matrix *
    monsterCo1GeometryVectorPoint77InverseMatrix = 1 :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
      ![8446081, 10417350, 964497, 1996049, 16, 57520, 58384, 1040, 24784, 26272, 8389632,
        10749659, 9364182, 1049297, 8413398, 9471494, 5716247, 2228544, 2266793, 5417567,
        2115500, 2131328, 2803725, 8389840]
      ![57424, 3600533, 3585285, 423625, 16, 58609, 8445969, 58369, 41114, 8390496, 144,
        12597261, 8443090, 8396957, 9629, 8390080, 10471575, 2228544, 9447591, 11696967, 49968,
        10502603, 15526728, 1168]
      ![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536,
        131072, 262144, 524288, 1048576, 2097152, 4194304, 8388608] hm hmi hi
      (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_inv monsterCo1GeometryVectorPoint77Transport _ _
    monsterCo1GeometryVectorPoint77Transport_binary hc v

/-- Source point 77 is the literal actual transported frame point. -/
def monsterCo1GeometryVectorPoint77 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryVectorPoint77Transport • monsterCo1GeometryBasePoint

/-- Complete binary coordinates of this literal actual source point. -/
theorem monsterCo1GeometryVectorPoint77_binary :
    monsterCo1GeometryVectorPoint77.val =
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0] := by
  change co1BinaryAction monsterCo1GeometryVectorPoint77Transport monsterCo1GeometryBasePoint.val =
      _
  rw [monsterCo1GeometryVectorPoint77Transport_binary, monsterCo1GeometryBasePoint_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
