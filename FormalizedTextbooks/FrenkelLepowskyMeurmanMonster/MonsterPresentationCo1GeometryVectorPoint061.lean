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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint029

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The literal actual two-core word for source point 61. -/
def monsterCo1GeometryVectorPoint61Transport : Co1 :=
  monsterCo1GeometryVectorPoint10Transport * monsterCo1GeometryTransportOperator 5 *
    monsterCo1GeometryVectorPoint10Transport⁻¹ * monsterCo1GeometryVectorPoint29Transport

/-- Complete displayed binary matrix of actual transport 61. -/
def monsterCo1GeometryVectorPoint61Matrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  ![![0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 0, 0, 1],
    ![0, 1, 1, 1, 0, 1, 1, 1, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 0, 1],
    ![0, 1, 1, 1, 1, 0, 1, 1, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![1, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 1, 1, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 1],
    ![0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 1, 0],
    ![0, 1, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 0, 1],
    ![1, 1, 1, 0, 0, 0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1],
    ![0, 1, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1],
    ![0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
    ![0, 0, 0, 1, 1, 0, 0, 1, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1],
    ![1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 0],
    ![0, 0, 1, 1, 0, 0, 0, 1, 0, 1, 1, 1, 0, 0, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1],
    ![0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 1, 1],
    ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]]

/-- First complete finite matrix product in literal actual transport 61. -/
def monsterCo1GeometryVectorPoint61AfterSignMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  ![![1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 1, 1],
    ![1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 0],
    ![1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 0],
    ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![1, 1, 0, 1, 1, 1, 0, 0, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0],
    ![0, 0, 1, 1, 1, 1, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1],
    ![1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0],
    ![0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1],
    ![0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0],
    ![1, 0, 0, 1, 1, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 1, 1, 0, 0, 1, 0, 0, 0],
    ![0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1],
    ![1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 1],
    ![0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1],
    ![0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0],
    ![1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1]]

/-- Second complete finite matrix product in literal actual transport 61. -/
def monsterCo1GeometryVectorPoint61AfterInverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0],
    ![1, 1, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 1, 1, 0, 1, 0, 1],
    ![1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0],
    ![0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 0, 0],
    ![0, 0, 1, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 1],
    ![1, 1, 0, 1, 0, 1, 1, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 1],
    ![1, 1, 1, 0, 0, 1, 1, 1, 1, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1],
    ![0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 1],
    ![0, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 1, 0, 0],
    ![0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 0],
    ![0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0, 1],
    ![1, 1, 0, 1, 0, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![1, 0, 0, 0, 0, 1, 1, 1, 0, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1],
    ![1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1],
    ![1, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1]]

set_option maxHeartbeats 24000000 in
-- Check every entry of this finite actual transport matrix in the Lean kernel.
/-- Every column of transport 61 is its actual Conway binary action. -/
theorem monsterCo1GeometryVectorPoint61Transport_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint61Transport v =
      monsterCo1GeometryVectorPoint61Matrix *ᵥ v := by
  have hx : monsterCo1GeometryVectorPoint10Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![161, 12635279, 15788942, 14739854, 8445968, 8389680, 8446144, 8446016, 8421584, 8405104,
    8389632, 5732571, 13637663, 9470977, 2146544, 3186912, 1290874, 12762360, 15235412,
    6086281, 10535770, 1719, 338093, 58368] := by decide +kernel
  have hxi : monsterCo1GeometryVectorPoint10InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![8388849, 9292920, 11397572, 1960382, 8389648, 8388656, 8389760, 192, 8405147, 49484,
    8446177, 8380771, 8402563, 8446737, 58945, 8447409, 11731829, 2233916, 12321148, 9762476,
    49472, 17296, 4336290, 8447201] := by decide +kernel
  have hy : monsterCo1GeometryVectorPoint29Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![57552, 8442048, 8450752, 45744, 57520, 1152, 8388640, 57440, 49968, 49472, 8388768,
    2599355, 8736856, 1074042, 9462999, 876, 3430303, 15161819, 7986139, 10593822, 3196587,
    10503371, 14568157, 8389632] := by decide +kernel
  have he : monsterCo1GeometryVectorPoint61AfterSignMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![161, 12701184, 7465959, 6416747, 8446000, 1072, 57568, 57440, 8422320, 8405392, 8389632,
    5667131, 13703356, 1083373, 10535610, 3187046, 1291033, 12827928, 15301111, 14540192,
    2146576, 8390327, 8661006, 8447008] := by decide +kernel
  have hf : monsterCo1GeometryVectorPoint61AfterInverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![1, 921096, 11405935, 1968857, 8388640, 8447169, 58513, 58449, 8422503, 8406763, 1024,
    3362718, 4120332, 11551036, 9454827, 10544615, 9210018, 3229598, 3854092, 10915644,
    8389867, 10544353, 16657389, 8447185] := by decide +kernel
  have hc : monsterCo1GeometryVectorPoint61Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![57552, 10026741, 12089582, 11065566, 8388736, 241, 58465, 8389665, 8438204, 9488215,
    8388768, 7656440, 10320518, 34247, 10535100, 10527114, 16770866, 11805592, 6418693,
    10079884, 25280, 10502330, 13001842, 57409] := by decide +kernel
  have hc1 : monsterCo1GeometryVectorPoint10Matrix *
    monsterCo1GeometryTransportOperatorMatrix 5 =
    monsterCo1GeometryVectorPoint61AfterSignMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![161, 12635279, 15788942, 14739854, 8445968, 8389680, 8446144, 8446016, 8421584, 8405104,
    8389632, 5732571, 13637663, 9470977, 2146544, 3186912, 1290874, 12762360, 15235412,
    6086281, 10535770, 1719, 338093, 58368]
      (monsterCo1GeometryBinaryOperatorMasks 5)
    ![161, 12701184, 7465959, 6416747, 8446000, 1072, 57568, 57440, 8422320, 8405392, 8389632,
    5667131, 13703356, 1083373, 10535610, 3187046, 1291033, 12827928, 15301111, 14540192,
    2146576, 8390327, 8661006, 8447008] hx (monsterCo1GeometryBinaryOperatorMasks_decode 5) he
    (by decide +kernel)
  have hc2 : monsterCo1GeometryVectorPoint61AfterSignMatrix *
    monsterCo1GeometryVectorPoint10InverseMatrix =
    monsterCo1GeometryVectorPoint61AfterInverseMatrix :=
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
  have hc3 : monsterCo1GeometryVectorPoint61AfterInverseMatrix *
    monsterCo1GeometryVectorPoint29Matrix = monsterCo1GeometryVectorPoint61Matrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![1, 921096, 11405935, 1968857, 8388640, 8447169, 58513, 58449, 8422503, 8406763, 1024,
    3362718, 4120332, 11551036, 9454827, 10544615, 9210018, 3229598, 3854092, 10915644,
    8389867, 10544353, 16657389, 8447185]
    ![57552, 8442048, 8450752, 45744, 57520, 1152, 8388640, 57440, 49968, 49472, 8388768,
    2599355, 8736856, 1074042, 9462999, 876, 3430303, 15161819, 7986139, 10593822, 3196587,
    10503371, 14568157, 8389632]
    ![57552, 10026741, 12089582, 11065566, 8388736, 241, 58465, 8389665, 8438204, 9488215,
    8388768, 7656440, 10320518, 34247, 10535100, 10527114, 16770866, 11805592, 6418693,
    10079884, 25280, 10502330, 13001842, 57409] hf hy hc (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_line_products
    monsterCo1GeometryVectorPoint10Transport monsterCo1GeometryVectorPoint29Transport 5
    monsterCo1GeometryVectorPoint10Matrix monsterCo1GeometryVectorPoint10InverseMatrix
    monsterCo1GeometryVectorPoint29Matrix
    monsterCo1GeometryVectorPoint61AfterSignMatrix
    monsterCo1GeometryVectorPoint61AfterInverseMatrix monsterCo1GeometryVectorPoint61Matrix
    monsterCo1GeometryVectorPoint10Transport_binary
    monsterCo1GeometryVectorPoint10Transport_inverse_binary
    monsterCo1GeometryVectorPoint29Transport_binary
    hc1 hc2 hc3 v

/-- Source point 61 is the literal actual transported frame point. -/
def monsterCo1GeometryVectorPoint61 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryVectorPoint61Transport • monsterCo1GeometryBasePoint

/-- Complete binary coordinates of this literal actual source point. -/
theorem monsterCo1GeometryVectorPoint61_binary :
    monsterCo1GeometryVectorPoint61.val =
      ![0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0] := by
  change co1BinaryAction monsterCo1GeometryVectorPoint61Transport monsterCo1GeometryBasePoint.val =
      _
  rw [monsterCo1GeometryVectorPoint61Transport_binary, monsterCo1GeometryBasePoint_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
