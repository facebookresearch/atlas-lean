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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint021
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint086

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The literal actual two-core word for source point 134. -/
def monsterCo1GeometryVectorPoint134Transport : Co1 :=
  monsterCo1GeometryVectorPoint21Transport * monsterCo1GeometryTransportOperator 5 *
    monsterCo1GeometryVectorPoint21Transport⁻¹ * monsterCo1GeometryVectorPoint86Transport

/-- Complete displayed binary matrix of actual transport 134. -/
def monsterCo1GeometryVectorPoint134Matrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![9331347, 9845524, 636484, 9352481, 9331444, 9306546, 942659, 590695, 9037046, 1634164,
      614465, 4228536, 10951495, 15631486, 4722137, 2198388, 10742750, 9653300, 12611287,
      7579964, 4686692, 6350826, 16545012, 33719]

/-- First complete finite matrix product in literal actual transport 134. -/
def monsterCo1GeometryVectorPoint134AfterSignMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![364912, 5213805, 684768, 704528, 8754976, 8738672, 8754640, 8767088, 8716509, 12955008,
      8717952, 9823523, 16017290, 10786105, 15829272, 5607249, 5071611, 3004903, 2758978,
      9006330, 2196041, 10560281, 13870682, 8397824]

/-- Second complete finite matrix product in literal actual transport 134. -/
def monsterCo1GeometryVectorPoint134AfterInverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![7889220, 13408979, 7672287, 663893, 5783993, 7897842, 7889157, 505091, 481044, 13000140,
      2585336, 2109243, 9301938, 9071153, 3461368, 14765428, 13887503, 12783119, 6483980,
      6513413, 12441737, 13773987, 12061225, 10495803]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 24000000 in
-- Check every entry of this finite actual transport matrix in the Lean kernel.
/-- Every column of transport 134 is its actual Conway binary action. -/
theorem monsterCo1GeometryVectorPoint134Transport_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint134Transport v =
      monsterCo1GeometryVectorPoint134Matrix *ᵥ v := by
  have hx : monsterCo1GeometryVectorPoint21Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![8753212, 13536263, 9073289, 9093529, 8754796, 349372, 365724, 378620, 328401, 12889667,
    8717452, 1435523, 16017024, 2397375, 15764017, 5541566, 13459633, 11328136, 11213486,
    552115, 10584547, 10559859, 5482265, 9888] := by decide +kernel
  have hxi : monsterCo1GeometryVectorPoint21InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![479330, 10505873, 9093297, 11384110, 14620496, 58432, 16724027, 57584, 8389645, 871,
    2106397, 6419317, 11593622, 10494922, 5189706, 5231722, 2004638, 728030, 3736320, 14600699,
    8423168, 12143725, 15674507, 2105580] := by decide +kernel
  have hy : monsterCo1GeometryVectorPoint86Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![8388624, 36864, 8401904, 8409568, 16, 58416, 192, 64, 24784, 41072, 58368, 12583439,
    13637663, 9470977, 10494192, 11550944, 13831748, 131270, 11060699, 1860102, 11536267,
    1049286, 8581833, 8389632] := by rfl
  have he : monsterCo1GeometryVectorPoint134AfterSignMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![364912, 5213805, 684768, 704528, 8754976, 8738672, 8754640, 8767088, 8716509, 12955008,
    8717952, 9823523, 16017290, 10786105, 15829272, 5607249, 5071611, 3004903, 2758978,
    9006330, 2196041, 10560281, 13870682, 8397824] := by rfl
  have hf : monsterCo1GeometryVectorPoint134AfterInverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![7889220, 13408979, 7672287, 663893, 5783993, 7897842, 7889157, 505091, 481044, 13000140,
    2585336, 2109243, 9301938, 9071153, 3461368, 14765428, 13887503, 12783119, 6483980,
    6513413, 12441737, 13773987, 12061225, 10495803] := by rfl
  have hc : monsterCo1GeometryVectorPoint134Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![9331347, 9845524, 636484, 9352481, 9331444, 9306546, 942659, 590695, 9037046, 1634164,
    614465, 4228536, 10951495, 15631486, 4722137, 2198388, 10742750, 9653300, 12611287,
    7579964, 4686692, 6350826, 16545012, 33719] := by rfl
  have hc1 : monsterCo1GeometryVectorPoint21Matrix *
    monsterCo1GeometryTransportOperatorMatrix 5 =
    monsterCo1GeometryVectorPoint134AfterSignMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![8753212, 13536263, 9073289, 9093529, 8754796, 349372, 365724, 378620, 328401, 12889667,
    8717452, 1435523, 16017024, 2397375, 15764017, 5541566, 13459633, 11328136, 11213486,
    552115, 10584547, 10559859, 5482265, 9888]
      (monsterCo1GeometryBinaryOperatorMasks 5)
    ![364912, 5213805, 684768, 704528, 8754976, 8738672, 8754640, 8767088, 8716509, 12955008,
    8717952, 9823523, 16017290, 10786105, 15829272, 5607249, 5071611, 3004903, 2758978,
    9006330, 2196041, 10560281, 13870682, 8397824] hx
    (monsterCo1GeometryBinaryOperatorMasks_decode 5) he (by decide +kernel)
  have hc2 : monsterCo1GeometryVectorPoint134AfterSignMatrix *
    monsterCo1GeometryVectorPoint21InverseMatrix =
    monsterCo1GeometryVectorPoint134AfterInverseMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![364912, 5213805, 684768, 704528, 8754976, 8738672, 8754640, 8767088, 8716509, 12955008,
    8717952, 9823523, 16017290, 10786105, 15829272, 5607249, 5071611, 3004903, 2758978,
    9006330, 2196041, 10560281, 13870682, 8397824]
    ![479330, 10505873, 9093297, 11384110, 14620496, 58432, 16724027, 57584, 8389645, 871,
    2106397, 6419317, 11593622, 10494922, 5189706, 5231722, 2004638, 728030, 3736320, 14600699,
    8423168, 12143725, 15674507, 2105580]
    ![7889220, 13408979, 7672287, 663893, 5783993, 7897842, 7889157, 505091, 481044, 13000140,
    2585336, 2109243, 9301938, 9071153, 3461368, 14765428, 13887503, 12783119, 6483980,
    6513413, 12441737, 13773987, 12061225, 10495803] he hxi hf (by decide +kernel)
  have hc3 : monsterCo1GeometryVectorPoint134AfterInverseMatrix *
    monsterCo1GeometryVectorPoint86Matrix = monsterCo1GeometryVectorPoint134Matrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![7889220, 13408979, 7672287, 663893, 5783993, 7897842, 7889157, 505091, 481044, 13000140,
    2585336, 2109243, 9301938, 9071153, 3461368, 14765428, 13887503, 12783119, 6483980,
    6513413, 12441737, 13773987, 12061225, 10495803]
    ![8388624, 36864, 8401904, 8409568, 16, 58416, 192, 64, 24784, 41072, 58368, 12583439,
    13637663, 9470977, 10494192, 11550944, 13831748, 131270, 11060699, 1860102, 11536267,
    1049286, 8581833, 8389632]
    ![9331347, 9845524, 636484, 9352481, 9331444, 9306546, 942659, 590695, 9037046, 1634164,
    614465, 4228536, 10951495, 15631486, 4722137, 2198388, 10742750, 9653300, 12611287,
    7579964, 4686692, 6350826, 16545012, 33719] hf hy hc (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_line_products
    monsterCo1GeometryVectorPoint21Transport monsterCo1GeometryVectorPoint86Transport 5
    monsterCo1GeometryVectorPoint21Matrix monsterCo1GeometryVectorPoint21InverseMatrix
    monsterCo1GeometryVectorPoint86Matrix
    monsterCo1GeometryVectorPoint134AfterSignMatrix
    monsterCo1GeometryVectorPoint134AfterInverseMatrix monsterCo1GeometryVectorPoint134Matrix
    monsterCo1GeometryVectorPoint21Transport_binary
    monsterCo1GeometryVectorPoint21Transport_inverse_binary
    monsterCo1GeometryVectorPoint86Transport_binary
    hc1 hc2 hc3 v

/-- Source point 134 is the literal actual transported frame point. -/
def monsterCo1GeometryVectorPoint134 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryVectorPoint134Transport • monsterCo1GeometryBasePoint

/-- Complete binary coordinates of this literal actual source point. -/
theorem monsterCo1GeometryVectorPoint134_binary :
    monsterCo1GeometryVectorPoint134.val =
      ![0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0] := by
  change co1BinaryAction monsterCo1GeometryVectorPoint134Transport monsterCo1GeometryBasePoint.val =
      _
  rw [monsterCo1GeometryVectorPoint134Transport_binary, monsterCo1GeometryBasePoint_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
