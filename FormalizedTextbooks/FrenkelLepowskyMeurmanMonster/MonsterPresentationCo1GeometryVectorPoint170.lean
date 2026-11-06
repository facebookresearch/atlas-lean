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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint042
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint162

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The literal actual two-core word for source point 170. -/
def monsterCo1GeometryVectorPoint170Transport : Co1 :=
  monsterCo1GeometryVectorPoint42Transport * monsterCo1GeometryTransportOperator 5 *
    monsterCo1GeometryVectorPoint42Transport⁻¹ * monsterCo1GeometryVectorPoint162Transport

/-- Complete displayed binary matrix of actual transport 170. -/
def monsterCo1GeometryVectorPoint170Matrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![12575235, 3195142, 768, 3145798, 2032, 3203174, 9372008, 4136991, 9430569, 991401,
      992149, 9092418, 3397081, 8746717, 5285462, 13052236, 13021224, 12571660, 12523183,
      12681184, 611056, 7830846, 8623119, 8388848]

/-- First complete finite matrix product in literal actual transport 170. -/
def monsterCo1GeometryVectorPoint170AfterSignMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![128, 63168, 53856, 8446144, 37280, 49232, 49392, 21408, 29264, 45808, 8192, 8724013,
      1033056, 4537389, 12917888, 8725037, 10487265, 7522761, 6540101, 11536225, 10757961,
      11806149, 5294638, 8389632]

/-- Second complete finite matrix product in literal actual transport 170. -/
def monsterCo1GeometryVectorPoint170AfterInverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![1, 2, 8390642, 8389647, 8390223, 8390583, 8390615, 8389934, 8390462, 8390607, 8389622,
      8375547, 10981686, 16769805, 8357115, 12157958, 14042213, 14305173, 15026068, 15090788,
      8274019, 7815266, 12566780, 8388608]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 24000000 in
-- Check every entry of this finite actual transport matrix in the Lean kernel.
/-- Every column of transport 170 is its actual Conway binary action. -/
theorem monsterCo1GeometryVectorPoint170Transport_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint170Transport v =
      monsterCo1GeometryVectorPoint170Matrix *ᵥ v := by
  have hx : monsterCo1GeometryVectorPoint42Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![128, 63168, 8442048, 57568, 37600, 8438480, 8438384, 21088, 28976, 45840, 8397472,
    269326, 1032421, 4471982, 4464291, 336513, 10487083, 7588623, 6473999, 11536167, 2369327,
    3417391, 5359661, 8389632] := by decide +kernel
  have hxi : monsterCo1GeometryVectorPoint42InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![12148742, 7381770, 2024545, 2614369, 1065, 97, 8389391, 1, 1696, 1008, 1126, 4606096,
    2045, 8389622, 8390627, 8390514, 3538944, 6129559, 1040385, 4452367, 3146736, 7283116,
    8399766, 8389734] := by decide +kernel
  have hy : monsterCo1GeometryVectorPoint162Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![12575235, 3195142, 12575234, 3146534, 11543271, 9372265, 3203943, 3204970, 4177971,
    58577, 11584151, 14107333, 4862057, 6776920, 874961, 75817, 5603682, 2877516, 15542506,
    9718959, 6054623, 14962452, 14575848, 8388848] := by rfl
  have he : monsterCo1GeometryVectorPoint170AfterSignMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![128, 63168, 53856, 8446144, 37280, 49232, 49392, 21408, 29264, 45808, 8192, 8724013,
    1033056, 4537389, 12917888, 8725037, 10487265, 7522761, 6540101, 11536225, 10757961,
    11806149, 5294638, 8389632] := by rfl
  have hf : monsterCo1GeometryVectorPoint170AfterInverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![1, 2, 8390642, 8389647, 8390223, 8390583, 8390615, 8389934, 8390462, 8390607, 8389622,
    8375547, 10981686, 16769805, 8357115, 12157958, 14042213, 14305173, 15026068, 15090788,
    8274019, 7815266, 12566780, 8388608] := by rfl
  have hc : monsterCo1GeometryVectorPoint170Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![12575235, 3195142, 768, 3145798, 2032, 3203174, 9372008, 4136991, 9430569, 991401,
    992149, 9092418, 3397081, 8746717, 5285462, 13052236, 13021224, 12571660, 12523183,
    12681184, 611056, 7830846, 8623119, 8388848] := by rfl
  have hc1 : monsterCo1GeometryVectorPoint42Matrix *
    monsterCo1GeometryTransportOperatorMatrix 5 =
    monsterCo1GeometryVectorPoint170AfterSignMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![128, 63168, 8442048, 57568, 37600, 8438480, 8438384, 21088, 28976, 45840, 8397472,
    269326, 1032421, 4471982, 4464291, 336513, 10487083, 7588623, 6473999, 11536167, 2369327,
    3417391, 5359661, 8389632]
      (monsterCo1GeometryBinaryOperatorMasks 5)
    ![128, 63168, 53856, 8446144, 37280, 49232, 49392, 21408, 29264, 45808, 8192, 8724013,
    1033056, 4537389, 12917888, 8725037, 10487265, 7522761, 6540101, 11536225, 10757961,
    11806149, 5294638, 8389632] hx (monsterCo1GeometryBinaryOperatorMasks_decode 5) he (by
    decide +kernel)
  have hc2 : monsterCo1GeometryVectorPoint170AfterSignMatrix *
    monsterCo1GeometryVectorPoint42InverseMatrix =
    monsterCo1GeometryVectorPoint170AfterInverseMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![128, 63168, 53856, 8446144, 37280, 49232, 49392, 21408, 29264, 45808, 8192, 8724013,
    1033056, 4537389, 12917888, 8725037, 10487265, 7522761, 6540101, 11536225, 10757961,
    11806149, 5294638, 8389632]
    ![12148742, 7381770, 2024545, 2614369, 1065, 97, 8389391, 1, 1696, 1008, 1126, 4606096,
    2045, 8389622, 8390627, 8390514, 3538944, 6129559, 1040385, 4452367, 3146736, 7283116,
    8399766, 8389734]
    ![1, 2, 8390642, 8389647, 8390223, 8390583, 8390615, 8389934, 8390462, 8390607, 8389622,
    8375547, 10981686, 16769805, 8357115, 12157958, 14042213, 14305173, 15026068, 15090788,
    8274019, 7815266, 12566780, 8388608] he hxi hf (by decide +kernel)
  have hc3 : monsterCo1GeometryVectorPoint170AfterInverseMatrix *
    monsterCo1GeometryVectorPoint162Matrix = monsterCo1GeometryVectorPoint170Matrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![1, 2, 8390642, 8389647, 8390223, 8390583, 8390615, 8389934, 8390462, 8390607, 8389622,
    8375547, 10981686, 16769805, 8357115, 12157958, 14042213, 14305173, 15026068, 15090788,
    8274019, 7815266, 12566780, 8388608]
    ![12575235, 3195142, 12575234, 3146534, 11543271, 9372265, 3203943, 3204970, 4177971,
    58577, 11584151, 14107333, 4862057, 6776920, 874961, 75817, 5603682, 2877516, 15542506,
    9718959, 6054623, 14962452, 14575848, 8388848]
    ![12575235, 3195142, 768, 3145798, 2032, 3203174, 9372008, 4136991, 9430569, 991401,
    992149, 9092418, 3397081, 8746717, 5285462, 13052236, 13021224, 12571660, 12523183,
    12681184, 611056, 7830846, 8623119, 8388848] hf hy hc (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_line_products
    monsterCo1GeometryVectorPoint42Transport monsterCo1GeometryVectorPoint162Transport 5
    monsterCo1GeometryVectorPoint42Matrix monsterCo1GeometryVectorPoint42InverseMatrix
    monsterCo1GeometryVectorPoint162Matrix
    monsterCo1GeometryVectorPoint170AfterSignMatrix
    monsterCo1GeometryVectorPoint170AfterInverseMatrix monsterCo1GeometryVectorPoint170Matrix
    monsterCo1GeometryVectorPoint42Transport_binary
    monsterCo1GeometryVectorPoint42Transport_inverse_binary
    monsterCo1GeometryVectorPoint162Transport_binary
    hc1 hc2 hc3 v

/-- Source point 170 is the literal actual transported frame point. -/
def monsterCo1GeometryVectorPoint170 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryVectorPoint170Transport • monsterCo1GeometryBasePoint

/-- Complete binary coordinates of this literal actual source point. -/
theorem monsterCo1GeometryVectorPoint170_binary :
    monsterCo1GeometryVectorPoint170.val =
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0] := by
  change co1BinaryAction monsterCo1GeometryVectorPoint170Transport monsterCo1GeometryBasePoint.val =
      _
  rw [monsterCo1GeometryVectorPoint170Transport_binary, monsterCo1GeometryBasePoint_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
