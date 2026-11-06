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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint014
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint036

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The literal actual two-core word for source point 80. -/
def monsterCo1GeometryVectorPoint80Transport : Co1 :=
  monsterCo1GeometryVectorPoint14Transport * monsterCo1GeometryTransportOperator 7 *
    monsterCo1GeometryVectorPoint14Transport⁻¹ * monsterCo1GeometryVectorPoint36Transport

/-- Complete displayed binary matrix of actual transport 80. -/
def monsterCo1GeometryVectorPoint80Matrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![2802001, 12580190, 4864, 1380419, 11198477, 12576194, 12575134, 11198557, 7903938,
      7888590, 11191805, 9961409, 13067004, 16729196, 2097392, 6242449, 8605754, 8540726,
      570070, 6550583, 12935482, 4563162, 13084574, 49632]

/-- First complete finite matrix product in literal actual transport 80. -/
def monsterCo1GeometryVectorPoint80AfterSignMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![4129314, 11155266, 9819692, 1434764, 4183762, 4187442, 12576194, 4183522, 4472601,
      12860629, 4130274, 16464000, 475111, 196869, 11780146, 3195383, 5285543, 5330407,
      14849575, 14706529, 12354599, 3950023, 8911240, 50720]

/-- Second complete finite matrix product in literal actual transport 80. -/
def monsterCo1GeometryVectorPoint80AfterInverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![11969419, 7966856, 4, 8335490, 434192, 13210795, 7966922, 434304, 10794050, 1356611,
      435083, 1187528, 6428738, 7772417, 17248, 12992096, 66400, 131164, 11798333, 13548800,
      6299350, 14687580, 9571272, 8390539]

set_option maxHeartbeats 24000000 in
-- Check every entry of this finite actual transport matrix in the Lean kernel.
/-- Every column of transport 80 is its actual Conway binary action. -/
theorem monsterCo1GeometryVectorPoint80Transport_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint80Transport v =
      monsterCo1GeometryVectorPoint80Matrix *ᵥ v := by
  have hx : monsterCo1GeometryVectorPoint14Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![4129584, 11155152, 9819692, 9823788, 12572128, 12575904, 12575824, 12572368, 12598711,
    12598907, 12518640, 8338236, 212047, 196611, 11780878, 11584461, 5285275, 5330007, 6460587,
    6317671, 3966339, 3950147, 260096, 50176] := by decide +kernel
  have hxi : monsterCo1GeometryVectorPoint14InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![12149857, 11969681, 1035948, 1035612, 13620263, 13579335, 13619968, 13579008, 13620028,
    13579212, 11534576, 8380428, 3146747, 3146743, 9486509, 10535005, 16527408, 15978688,
    7152297, 5972312, 9507100, 11072140, 8383473, 11535361] := by decide +kernel
  have hy : monsterCo1GeometryVectorPoint36Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![8446976, 8392704, 4864, 4352, 8389648, 8389680, 8389824, 8389696, 8414416, 8430704,
    58368, 12919938, 5299343, 9437345, 2146464, 3195040, 8622186, 8540390, 554234, 832598,
    1754, 1654, 13686945, 8389632] := by decide +kernel
  have he : monsterCo1GeometryVectorPoint80AfterSignMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![4129314, 11155266, 9819692, 1434764, 4183762, 4187442, 12576194, 4183522, 4472601,
    12860629, 4130274, 16464000, 475111, 196869, 11780146, 3195383, 5285543, 5330407, 14849575,
    14706529, 12354599, 3950023, 8911240, 50720] := by rfl
  have hf : monsterCo1GeometryVectorPoint80AfterInverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![11969419, 7966856, 4, 8335490, 434192, 13210795, 7966922, 434304, 10794050, 1356611,
    435083, 1187528, 6428738, 7772417, 17248, 12992096, 66400, 131164, 11798333, 13548800,
    6299350, 14687580, 9571272, 8390539] := by rfl
  have hc : monsterCo1GeometryVectorPoint80Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![2802001, 12580190, 4864, 1380419, 11198477, 12576194, 12575134, 11198557, 7903938,
    7888590, 11191805, 9961409, 13067004, 16729196, 2097392, 6242449, 8605754, 8540726, 570070,
    6550583, 12935482, 4563162, 13084574, 49632] := by rfl
  have hc1 : monsterCo1GeometryVectorPoint14Matrix *
    monsterCo1GeometryTransportOperatorMatrix 7 =
    monsterCo1GeometryVectorPoint80AfterSignMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![4129584, 11155152, 9819692, 9823788, 12572128, 12575904, 12575824, 12572368, 12598711,
    12598907, 12518640, 8338236, 212047, 196611, 11780878, 11584461, 5285275, 5330007, 6460587,
    6317671, 3966339, 3950147, 260096, 50176]
      (monsterCo1GeometryBinaryOperatorMasks 7)
    ![4129314, 11155266, 9819692, 1434764, 4183762, 4187442, 12576194, 4183522, 4472601,
    12860629, 4130274, 16464000, 475111, 196869, 11780146, 3195383, 5285543, 5330407, 14849575,
    14706529, 12354599, 3950023, 8911240, 50720] hx
    (monsterCo1GeometryBinaryOperatorMasks_decode 7) he (by decide +kernel)
  have hc2 : monsterCo1GeometryVectorPoint80AfterSignMatrix *
    monsterCo1GeometryVectorPoint14InverseMatrix =
    monsterCo1GeometryVectorPoint80AfterInverseMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![4129314, 11155266, 9819692, 1434764, 4183762, 4187442, 12576194, 4183522, 4472601,
    12860629, 4130274, 16464000, 475111, 196869, 11780146, 3195383, 5285543, 5330407, 14849575,
    14706529, 12354599, 3950023, 8911240, 50720]
    ![12149857, 11969681, 1035948, 1035612, 13620263, 13579335, 13619968, 13579008, 13620028,
    13579212, 11534576, 8380428, 3146747, 3146743, 9486509, 10535005, 16527408, 15978688,
    7152297, 5972312, 9507100, 11072140, 8383473, 11535361]
    ![11969419, 7966856, 4, 8335490, 434192, 13210795, 7966922, 434304, 10794050, 1356611,
    435083, 1187528, 6428738, 7772417, 17248, 12992096, 66400, 131164, 11798333, 13548800,
    6299350, 14687580, 9571272, 8390539] he hxi hf (by decide +kernel)
  have hc3 : monsterCo1GeometryVectorPoint80AfterInverseMatrix *
    monsterCo1GeometryVectorPoint36Matrix = monsterCo1GeometryVectorPoint80Matrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![11969419, 7966856, 4, 8335490, 434192, 13210795, 7966922, 434304, 10794050, 1356611,
    435083, 1187528, 6428738, 7772417, 17248, 12992096, 66400, 131164, 11798333, 13548800,
    6299350, 14687580, 9571272, 8390539]
    ![8446976, 8392704, 4864, 4352, 8389648, 8389680, 8389824, 8389696, 8414416, 8430704,
    58368, 12919938, 5299343, 9437345, 2146464, 3195040, 8622186, 8540390, 554234, 832598,
    1754, 1654, 13686945, 8389632]
    ![2802001, 12580190, 4864, 1380419, 11198477, 12576194, 12575134, 11198557, 7903938,
    7888590, 11191805, 9961409, 13067004, 16729196, 2097392, 6242449, 8605754, 8540726, 570070,
    6550583, 12935482, 4563162, 13084574, 49632] hf hy hc (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_line_products
    monsterCo1GeometryVectorPoint14Transport monsterCo1GeometryVectorPoint36Transport 7
    monsterCo1GeometryVectorPoint14Matrix monsterCo1GeometryVectorPoint14InverseMatrix
    monsterCo1GeometryVectorPoint36Matrix
    monsterCo1GeometryVectorPoint80AfterSignMatrix
    monsterCo1GeometryVectorPoint80AfterInverseMatrix monsterCo1GeometryVectorPoint80Matrix
    monsterCo1GeometryVectorPoint14Transport_binary
    monsterCo1GeometryVectorPoint14Transport_inverse_binary
    monsterCo1GeometryVectorPoint36Transport_binary
    hc1 hc2 hc3 v

/-- Source point 80 is the literal actual transported frame point. -/
def monsterCo1GeometryVectorPoint80 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryVectorPoint80Transport • monsterCo1GeometryBasePoint

/-- Complete binary coordinates of this literal actual source point. -/
theorem monsterCo1GeometryVectorPoint80_binary :
    monsterCo1GeometryVectorPoint80.val =
      ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  change co1BinaryAction monsterCo1GeometryVectorPoint80Transport monsterCo1GeometryBasePoint.val =
      _
  rw [monsterCo1GeometryVectorPoint80Transport_binary, monsterCo1GeometryBasePoint_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
