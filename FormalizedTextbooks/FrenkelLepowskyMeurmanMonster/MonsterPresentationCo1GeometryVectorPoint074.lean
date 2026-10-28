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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint010
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint035

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The literal actual two-core word for source point 74. -/
def monsterCo1GeometryVectorPoint74Transport : Co1 :=
  monsterCo1GeometryVectorPoint10Transport * monsterCo1GeometryTransportOperator 5 *
    monsterCo1GeometryVectorPoint10Transport⁻¹ * monsterCo1GeometryVectorPoint35Transport

/-- Complete displayed binary matrix of actual transport 74. -/
def monsterCo1GeometryVectorPoint74Matrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![8388609, 11986453, 8840755, 11985662, 8446000, 8388736, 57424, 57552, 8390640, 8431040,
      8389632, 10553310, 8811112, 3179868, 8390090, 3179703, 10756562, 7568665, 6216733,
      8059371, 2097328, 8388710, 14058200, 8388752]

/-- First complete finite matrix product in literal actual transport 74. -/
def monsterCo1GeometryVectorPoint74AfterSignMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![161, 12701184, 7465959, 6416747, 8446000, 1072, 57568, 57440, 8422320, 8405392, 8389632,
      5667131, 13703356, 1083373, 10535610, 3187046, 1291033, 12827928, 15301111, 14540192,
      2146576, 8390327, 8661006, 8447008]

/-- Second complete finite matrix product in literal actual transport 74. -/
def monsterCo1GeometryVectorPoint74AfterInverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  monsterCo1GeometryBinaryMaskMatrix
    ![1, 921096, 11405935, 1968857, 8388640, 8447169, 58513, 58449, 8422503, 8406763, 1024,
      3362718, 4120332, 11551036, 9454827, 10544615, 9210018, 3229598, 3854092, 10915644,
      8389867, 10544353, 16657389, 8447185]

set_option maxHeartbeats 24000000 in
-- Check every entry of this finite actual transport matrix in the Lean kernel.
/-- Every column of transport 74 is its actual Conway binary action. -/
theorem monsterCo1GeometryVectorPoint74Transport_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint74Transport v =
      monsterCo1GeometryVectorPoint74Matrix *ᵥ v := by
  have hx : monsterCo1GeometryVectorPoint10Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![161, 12635279, 15788942, 14739854, 8445968, 8389680, 8446144, 8446016, 8421584, 8405104,
    8389632, 5732571, 13637663, 9470977, 2146544, 3186912, 1290874, 12762360, 15235412,
    6086281, 10535770, 1719, 338093, 58368] := by decide +kernel
  have hxi : monsterCo1GeometryVectorPoint10InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![8388849, 9292920, 11397572, 1960382, 8389648, 8388656, 8389760, 192, 8405147, 49484,
    8446177, 8380771, 8402563, 8446737, 58945, 8447409, 11731829, 2233916, 12321148, 9762476,
    49472, 17296, 4336290, 8447201] := by decide +kernel
  have hy : monsterCo1GeometryVectorPoint35Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![8388609, 4201487, 15792142, 14743566, 16, 48, 192, 64, 24784, 41072, 8389632, 13638145,
    13635087, 1107457, 10487040, 11536128, 237642, 155846, 565370, 811222, 122, 214, 65039,
    8445952] := by decide +kernel
  have he : monsterCo1GeometryVectorPoint74AfterSignMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![161, 12701184, 7465959, 6416747, 8446000, 1072, 57568, 57440, 8422320, 8405392, 8389632,
    5667131, 13703356, 1083373, 10535610, 3187046, 1291033, 12827928, 15301111, 14540192,
    2146576, 8390327, 8661006, 8447008] := by rfl
  have hf : monsterCo1GeometryVectorPoint74AfterInverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![1, 921096, 11405935, 1968857, 8388640, 8447169, 58513, 58449, 8422503, 8406763, 1024,
    3362718, 4120332, 11551036, 9454827, 10544615, 9210018, 3229598, 3854092, 10915644,
    8389867, 10544353, 16657389, 8447185] := by rfl
  have hc : monsterCo1GeometryVectorPoint74Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![8388609, 11986453, 8840755, 11985662, 8446000, 8388736, 57424, 57552, 8390640, 8431040,
    8389632, 10553310, 8811112, 3179868, 8390090, 3179703, 10756562, 7568665, 6216733, 8059371,
    2097328, 8388710, 14058200, 8388752] := by rfl
  have hc1 : monsterCo1GeometryVectorPoint10Matrix *
    monsterCo1GeometryTransportOperatorMatrix 5 =
    monsterCo1GeometryVectorPoint74AfterSignMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![161, 12635279, 15788942, 14739854, 8445968, 8389680, 8446144, 8446016, 8421584, 8405104,
    8389632, 5732571, 13637663, 9470977, 2146544, 3186912, 1290874, 12762360, 15235412,
    6086281, 10535770, 1719, 338093, 58368]
      (monsterCo1GeometryBinaryOperatorMasks 5)
    ![161, 12701184, 7465959, 6416747, 8446000, 1072, 57568, 57440, 8422320, 8405392, 8389632,
    5667131, 13703356, 1083373, 10535610, 3187046, 1291033, 12827928, 15301111, 14540192,
    2146576, 8390327, 8661006, 8447008] hx (monsterCo1GeometryBinaryOperatorMasks_decode 5) he
    (by decide +kernel)
  have hc2 : monsterCo1GeometryVectorPoint74AfterSignMatrix *
    monsterCo1GeometryVectorPoint10InverseMatrix =
    monsterCo1GeometryVectorPoint74AfterInverseMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![161, 12701184, 7465959, 6416747, 8446000, 1072, 57568, 57440, 8422320, 8405392, 8389632,
    5667131, 13703356, 1083373, 10535610, 3187046, 1291033, 12827928, 15301111, 14540192,
    2146576, 8390327, 8661006, 8447008]
    ![8388849, 9292920, 11397572, 1960382, 8389648, 8388656, 8389760, 192, 8405147, 49484,
    8446177, 8380771, 8402563, 8446737, 58945, 8447409, 11731829, 2233916, 12321148, 9762476,
    49472, 17296, 4336290, 8447201]
    ![1, 921096, 11405935, 1968857, 8388640, 8447169, 58513, 58449, 8422503, 8406763, 1024,
    3362718, 4120332, 11551036, 9454827, 10544615, 9210018, 3229598, 3854092, 10915644,
    8389867, 10544353, 16657389, 8447185] he hxi hf (by decide +kernel)
  have hc3 : monsterCo1GeometryVectorPoint74AfterInverseMatrix *
    monsterCo1GeometryVectorPoint35Matrix = monsterCo1GeometryVectorPoint74Matrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![1, 921096, 11405935, 1968857, 8388640, 8447169, 58513, 58449, 8422503, 8406763, 1024,
    3362718, 4120332, 11551036, 9454827, 10544615, 9210018, 3229598, 3854092, 10915644,
    8389867, 10544353, 16657389, 8447185]
    ![8388609, 4201487, 15792142, 14743566, 16, 48, 192, 64, 24784, 41072, 8389632, 13638145,
    13635087, 1107457, 10487040, 11536128, 237642, 155846, 565370, 811222, 122, 214, 65039,
    8445952]
    ![8388609, 11986453, 8840755, 11985662, 8446000, 8388736, 57424, 57552, 8390640, 8431040,
    8389632, 10553310, 8811112, 3179868, 8390090, 3179703, 10756562, 7568665, 6216733, 8059371,
    2097328, 8388710, 14058200, 8388752] hf hy hc (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_line_products
    monsterCo1GeometryVectorPoint10Transport monsterCo1GeometryVectorPoint35Transport 5
    monsterCo1GeometryVectorPoint10Matrix monsterCo1GeometryVectorPoint10InverseMatrix
    monsterCo1GeometryVectorPoint35Matrix
    monsterCo1GeometryVectorPoint74AfterSignMatrix
    monsterCo1GeometryVectorPoint74AfterInverseMatrix monsterCo1GeometryVectorPoint74Matrix
    monsterCo1GeometryVectorPoint10Transport_binary
    monsterCo1GeometryVectorPoint10Transport_inverse_binary
    monsterCo1GeometryVectorPoint35Transport_binary
    hc1 hc2 hc3 v

/-- Source point 74 is the literal actual transported frame point. -/
def monsterCo1GeometryVectorPoint74 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryVectorPoint74Transport • monsterCo1GeometryBasePoint

/-- Complete binary coordinates of this literal actual source point. -/
theorem monsterCo1GeometryVectorPoint74_binary :
    monsterCo1GeometryVectorPoint74.val =
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0] := by
  change co1BinaryAction monsterCo1GeometryVectorPoint74Transport monsterCo1GeometryBasePoint.val =
      _
  rw [monsterCo1GeometryVectorPoint74Transport_binary, monsterCo1GeometryBasePoint_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
