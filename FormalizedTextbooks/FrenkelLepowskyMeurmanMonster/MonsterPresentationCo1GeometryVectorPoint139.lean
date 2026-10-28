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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint053
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint088

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The literal actual two-core word for source point 139. -/
def monsterCo1GeometryVectorPoint139Transport : Co1 :=
  monsterCo1GeometryVectorPoint53Transport * monsterCo1GeometryTransportOperator 5 *
    monsterCo1GeometryVectorPoint53Transport⁻¹ * monsterCo1GeometryVectorPoint88Transport

/-- Complete displayed binary matrix of actual transport 139. -/
def monsterCo1GeometryVectorPoint139Matrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![14226809, 1489641, 6287747, 4186257, 5838319, 6887055, 5837080, 12181511, 3736465,
      11124195, 9036551, 3680230, 3657668, 16299878, 12089597, 1063333, 8028325, 15353460,
      3198192, 4326089, 13718801, 1130770, 8247915, 3203985]

/-- First complete finite matrix product in literal actual transport 139. -/
def monsterCo1GeometryVectorPoint139AfterSignMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![364912, 13609581, 9066208, 9102352, 8754976, 8738672, 8754640, 8767088, 337117, 4557184,
      8717952, 1431299, 3263575, 10749641, 15849544, 5590513, 548054, 6866634, 7276143,
      13390551, 10556857, 2209001, 9869943, 8397824]

/-- Second complete finite matrix product in literal actual transport 139. -/
def monsterCo1GeometryVectorPoint139AfterInverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![7889475, 6053252, 13973224, 11141779, 5785167, 7897589, 7889410, 504565, 2585384,
      14064279, 2585087, 2148445, 15439720, 6659552, 15409960, 13715829, 15370088, 5916255,
      13327163, 7007234, 5385311, 4053109, 90547, 10494922]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 24000000 in
-- Check every entry of this finite actual transport matrix in the Lean kernel.
/-- Every column of transport 139 is its actual Conway binary action. -/
theorem monsterCo1GeometryVectorPoint139Transport_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint139Transport v =
      monsterCo1GeometryVectorPoint139Matrix *ᵥ v := by
  have hx : monsterCo1GeometryVectorPoint53Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![8753212, 13544103, 9065513, 9103161, 8754796, 349372, 365724, 378620, 337009, 12880099,
    8717452, 9819939, 11587230, 10748943, 7396001, 5525150, 9002527, 6866822, 7276448, 5001757,
    10556755, 10597827, 1547191, 9888] := by decide +kernel
  have hxi : monsterCo1GeometryVectorPoint53InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![8869780, 1092096, 9093309, 11384357, 14620496, 58432, 16725194, 57584, 8389645, 871,
    2105580, 14807827, 11593622, 10495803, 5190843, 5230747, 2004377, 12319812, 3736320,
    7220845, 8423264, 9022717, 14666619, 2106397] := by decide +kernel
  have hy : monsterCo1GeometryVectorPoint88Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![8388689, 4137102, 9372153, 983461, 8389680, 8445968, 1072, 8446016, 768, 8397296,
    8389632, 3680048, 12579042, 429, 11551738, 11552326, 15908739, 3364779, 7905070, 3364850,
    10486012, 8389991, 4522072, 8388848] := by rfl
  have he : monsterCo1GeometryVectorPoint139AfterSignMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![364912, 13609581, 9066208, 9102352, 8754976, 8738672, 8754640, 8767088, 337117, 4557184,
    8717952, 1431299, 3263575, 10749641, 15849544, 5590513, 548054, 6866634, 7276143, 13390551,
    10556857, 2209001, 9869943, 8397824] := by rfl
  have hf : monsterCo1GeometryVectorPoint139AfterInverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![7889475, 6053252, 13973224, 11141779, 5785167, 7897589, 7889410, 504565, 2585384,
    14064279, 2585087, 2148445, 15439720, 6659552, 15409960, 13715829, 15370088, 5916255,
    13327163, 7007234, 5385311, 4053109, 90547, 10494922] := by rfl
  have hc : monsterCo1GeometryVectorPoint139Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![14226809, 1489641, 6287747, 4186257, 5838319, 6887055, 5837080, 12181511, 3736465,
    11124195, 9036551, 3680230, 3657668, 16299878, 12089597, 1063333, 8028325, 15353460,
    3198192, 4326089, 13718801, 1130770, 8247915, 3203985] := by rfl
  have hc1 : monsterCo1GeometryVectorPoint53Matrix *
    monsterCo1GeometryTransportOperatorMatrix 5 =
    monsterCo1GeometryVectorPoint139AfterSignMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![8753212, 13544103, 9065513, 9103161, 8754796, 349372, 365724, 378620, 337009, 12880099,
    8717452, 9819939, 11587230, 10748943, 7396001, 5525150, 9002527, 6866822, 7276448, 5001757,
    10556755, 10597827, 1547191, 9888]
      (monsterCo1GeometryBinaryOperatorMasks 5)
    ![364912, 13609581, 9066208, 9102352, 8754976, 8738672, 8754640, 8767088, 337117, 4557184,
    8717952, 1431299, 3263575, 10749641, 15849544, 5590513, 548054, 6866634, 7276143, 13390551,
    10556857, 2209001, 9869943, 8397824] hx (monsterCo1GeometryBinaryOperatorMasks_decode 5) he
    (by decide +kernel)
  have hc2 : monsterCo1GeometryVectorPoint139AfterSignMatrix *
    monsterCo1GeometryVectorPoint53InverseMatrix =
    monsterCo1GeometryVectorPoint139AfterInverseMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![364912, 13609581, 9066208, 9102352, 8754976, 8738672, 8754640, 8767088, 337117, 4557184,
    8717952, 1431299, 3263575, 10749641, 15849544, 5590513, 548054, 6866634, 7276143, 13390551,
    10556857, 2209001, 9869943, 8397824]
    ![8869780, 1092096, 9093309, 11384357, 14620496, 58432, 16725194, 57584, 8389645, 871,
    2105580, 14807827, 11593622, 10495803, 5190843, 5230747, 2004377, 12319812, 3736320,
    7220845, 8423264, 9022717, 14666619, 2106397]
    ![7889475, 6053252, 13973224, 11141779, 5785167, 7897589, 7889410, 504565, 2585384,
    14064279, 2585087, 2148445, 15439720, 6659552, 15409960, 13715829, 15370088, 5916255,
    13327163, 7007234, 5385311, 4053109, 90547, 10494922] he hxi hf (by decide +kernel)
  have hc3 : monsterCo1GeometryVectorPoint139AfterInverseMatrix *
    monsterCo1GeometryVectorPoint88Matrix = monsterCo1GeometryVectorPoint139Matrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![7889475, 6053252, 13973224, 11141779, 5785167, 7897589, 7889410, 504565, 2585384,
    14064279, 2585087, 2148445, 15439720, 6659552, 15409960, 13715829, 15370088, 5916255,
    13327163, 7007234, 5385311, 4053109, 90547, 10494922]
    ![8388689, 4137102, 9372153, 983461, 8389680, 8445968, 1072, 8446016, 768, 8397296,
    8389632, 3680048, 12579042, 429, 11551738, 11552326, 15908739, 3364779, 7905070, 3364850,
    10486012, 8389991, 4522072, 8388848]
    ![14226809, 1489641, 6287747, 4186257, 5838319, 6887055, 5837080, 12181511, 3736465,
    11124195, 9036551, 3680230, 3657668, 16299878, 12089597, 1063333, 8028325, 15353460,
    3198192, 4326089, 13718801, 1130770, 8247915, 3203985] hf hy hc (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_line_products
    monsterCo1GeometryVectorPoint53Transport monsterCo1GeometryVectorPoint88Transport 5
    monsterCo1GeometryVectorPoint53Matrix monsterCo1GeometryVectorPoint53InverseMatrix
    monsterCo1GeometryVectorPoint88Matrix
    monsterCo1GeometryVectorPoint139AfterSignMatrix
    monsterCo1GeometryVectorPoint139AfterInverseMatrix monsterCo1GeometryVectorPoint139Matrix
    monsterCo1GeometryVectorPoint53Transport_binary
    monsterCo1GeometryVectorPoint53Transport_inverse_binary
    monsterCo1GeometryVectorPoint88Transport_binary
    hc1 hc2 hc3 v

/-- Source point 139 is the literal actual transported frame point. -/
def monsterCo1GeometryVectorPoint139 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryVectorPoint139Transport • monsterCo1GeometryBasePoint

/-- Complete binary coordinates of this literal actual source point. -/
theorem monsterCo1GeometryVectorPoint139_binary :
    monsterCo1GeometryVectorPoint139.val =
      ![0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0, 0, 0, 1, 0] := by
  change co1BinaryAction monsterCo1GeometryVectorPoint139Transport monsterCo1GeometryBasePoint.val =
      _
  rw [monsterCo1GeometryVectorPoint139Transport_binary, monsterCo1GeometryBasePoint_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
