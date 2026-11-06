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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint016
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint030

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The literal actual two-core word for source point 66. -/
def monsterCo1GeometryVectorPoint66Transport : Co1 :=
  monsterCo1GeometryVectorPoint16Transport * monsterCo1GeometryTransportOperator 6 *
    monsterCo1GeometryVectorPoint16Transport⁻¹ * monsterCo1GeometryVectorPoint30Transport

/-- Complete displayed binary matrix of actual transport 66. -/
def monsterCo1GeometryVectorPoint66Matrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  ![![0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0],
    ![0, 0, 1, 0, 0, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1],
    ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![1, 0, 0, 1, 1, 0, 0, 0, 1, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1],
    ![1, 1, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0],
    ![1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0],
    ![1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0],
    ![1, 1, 1, 1, 0, 1, 0, 1, 0, 0, 0, 1, 1, 1, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1],
    ![0, 0, 1, 1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0],
    ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0],
    ![0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![1, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 1, 0, 1, 1, 1, 0, 1, 0, 0, 0, 1, 1],
    ![0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0],
    ![1, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1],
    ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 1, 1, 1],
    ![0, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 1],
    ![0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1],
    ![1, 0, 1, 1, 1, 0, 0, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1],
    ![1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0],
    ![1, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 1, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 1],
    ![0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1],
    ![1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 1, 0, 0, 0, 1, 1, 1, 0, 1, 1, 0, 0, 1, 0],
    ![0, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1]]

/-- First complete finite matrix product in literal actual transport 66. -/
def monsterCo1GeometryVectorPoint66AfterSignMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1, 1, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 0, 1, 0, 1, 0],
    ![0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0],
    ![1, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 1, 0, 0, 1, 1, 1, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0, 0, 1, 0, 1, 1],
    ![1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 1],
    ![1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0],
    ![0, 1, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1],
    ![1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 1, 0],
    ![1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 1, 1, 1],
    ![0, 1, 1, 0, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 1, 1, 1, 0, 1, 0, 1, 0, 0, 0],
    ![0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 1, 1, 1, 1, 0, 1, 1],
    ![0, 1, 0, 1, 0, 0, 0, 1, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 1],
    ![0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0],
    ![1, 0, 1, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1],
    ![0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1, 1, 1, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
    ![0, 1, 1, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1],
    ![0, 1, 1, 1, 0, 0, 0, 1, 0, 0, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 0],
    ![0, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1],
    ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1]]

/-- Second complete finite matrix product in literal actual transport 66. -/
def monsterCo1GeometryVectorPoint66AfterInverseMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1, 0, 1, 0, 1, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 1, 1, 0, 0],
    ![0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 1, 1, 0, 0],
    ![1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![1, 0, 0, 0, 0, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0],
    ![1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0],
    ![1, 0, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 0, 0, 0, 1, 0, 0, 1, 1, 0],
    ![1, 0, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 0, 0, 1, 1, 1, 0, 1, 0],
    ![0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1, 0, 0],
    ![1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0],
    ![1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 0, 0],
    ![1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0],
    ![0, 1, 1, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 1, 1, 0, 0],
    ![0, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0],
    ![0, 0, 0, 1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 0],
    ![0, 0, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 1, 1, 1, 1],
    ![1, 0, 0, 1, 0, 1, 0, 0, 1, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 0, 0]]

set_option maxHeartbeats 24000000 in
-- Check every entry of this finite actual transport matrix in the Lean kernel.
/-- Every column of transport 66 is its actual Conway binary action. -/
theorem monsterCo1GeometryVectorPoint66Transport_binary (v : Fin 24 → ZMod 2) :
    co1BinaryAction monsterCo1GeometryVectorPoint66Transport v =
      monsterCo1GeometryVectorPoint66Matrix *ᵥ v := by
  have hx : monsterCo1GeometryVectorPoint16Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![128, 13691598, 12593359, 58593, 5270255, 9488081, 9487985, 5286511, 6327614, 7360286,
    9488032, 9815203, 6231749, 8712320, 323724, 8716416, 8388906, 209664, 143616, 8389414,
    10778801, 11843729, 13706275, 58368] := by decide +kernel
  have hxi : monsterCo1GeometryVectorPoint16InverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![871, 651110, 15182086, 14592518, 8389673, 97, 8389391, 1, 15672833, 3146496, 3761153,
    13002650, 9422593, 12149904, 3760261, 3760148, 3539712, 14517648, 1040385, 12841743,
    3145968, 7282849, 16157697, 3760896] := by decide +kernel
  have hy : monsterCo1GeometryVectorPoint30Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![8388800, 8451008, 61632, 29600, 57520, 32, 8388640, 57440, 49968, 49472, 8388768,
    12615680, 8738040, 1075162, 9461879, 1996, 3212038, 15161819, 6904285, 11600565, 3203078,
    11591776, 3946495, 8389632] := by decide +kernel
  have he : monsterCo1GeometryVectorPoint66AfterSignMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![128, 5433879, 4336016, 58609, 13789414, 9488215, 1099767, 13805862, 6459309, 15879179,
    1099558, 1426976, 14619674, 8713098, 324486, 8717189, 298, 209487, 143424, 806, 10909992,
    3586190, 13706682, 8446992] := by decide +kernel
  have hf : monsterCo1GeometryVectorPoint66AfterInverseMatrix = monsterCo1GeometryBinaryMaskMatrix
    ![1, 3819732, 3877042, 8389665, 675041, 90176, 3670816, 6646143, 6582201, 6057945, 3671904,
    33792, 3774502, 540769, 532577, 3673952, 3695360, 6146575, 7021838, 3236608, 8130264,
    7605688, 15829832, 3761961] := by decide +kernel
  have hc : monsterCo1GeometryVectorPoint66Matrix = monsterCo1GeometryBinaryMaskMatrix
    ![8388800, 412495, 12012772, 8389696, 8805145, 3212427, 3211395, 1333513, 10844335,
    1342076, 3211267, 8390508, 12964289, 2187778, 10577327, 15826947, 11601678, 11917580,
    16472861, 3212989, 10772033, 9789060, 5097123, 8419304] := by decide +kernel
  have hc1 : monsterCo1GeometryVectorPoint16Matrix *
    monsterCo1GeometryTransportOperatorMatrix 6 =
    monsterCo1GeometryVectorPoint66AfterSignMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![128, 13691598, 12593359, 58593, 5270255, 9488081, 9487985, 5286511, 6327614, 7360286,
    9488032, 9815203, 6231749, 8712320, 323724, 8716416, 8388906, 209664, 143616, 8389414,
    10778801, 11843729, 13706275, 58368]
      (monsterCo1GeometryBinaryOperatorMasks 6)
    ![128, 5433879, 4336016, 58609, 13789414, 9488215, 1099767, 13805862, 6459309, 15879179,
    1099558, 1426976, 14619674, 8713098, 324486, 8717189, 298, 209487, 143424, 806, 10909992,
    3586190, 13706682, 8446992] hx (monsterCo1GeometryBinaryOperatorMasks_decode 6) he (by
    decide +kernel)
  have hc2 : monsterCo1GeometryVectorPoint66AfterSignMatrix *
    monsterCo1GeometryVectorPoint16InverseMatrix =
    monsterCo1GeometryVectorPoint66AfterInverseMatrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![128, 5433879, 4336016, 58609, 13789414, 9488215, 1099767, 13805862, 6459309, 15879179,
    1099558, 1426976, 14619674, 8713098, 324486, 8717189, 298, 209487, 143424, 806, 10909992,
    3586190, 13706682, 8446992]
    ![871, 651110, 15182086, 14592518, 8389673, 97, 8389391, 1, 15672833, 3146496, 3761153,
    13002650, 9422593, 12149904, 3760261, 3760148, 3539712, 14517648, 1040385, 12841743,
    3145968, 7282849, 16157697, 3760896]
    ![1, 3819732, 3877042, 8389665, 675041, 90176, 3670816, 6646143, 6582201, 6057945, 3671904,
    33792, 3774502, 540769, 532577, 3673952, 3695360, 6146575, 7021838, 3236608, 8130264,
    7605688, 15829832, 3761961] he hxi hf (by decide +kernel)
  have hc3 : monsterCo1GeometryVectorPoint66AfterInverseMatrix *
    monsterCo1GeometryVectorPoint30Matrix = monsterCo1GeometryVectorPoint66Matrix :=
    monsterCo1GeometryBinaryMaskProduct_certificate _ _ _
    ![1, 3819732, 3877042, 8389665, 675041, 90176, 3670816, 6646143, 6582201, 6057945, 3671904,
    33792, 3774502, 540769, 532577, 3673952, 3695360, 6146575, 7021838, 3236608, 8130264,
    7605688, 15829832, 3761961]
    ![8388800, 8451008, 61632, 29600, 57520, 32, 8388640, 57440, 49968, 49472, 8388768,
    12615680, 8738040, 1075162, 9461879, 1996, 3212038, 15161819, 6904285, 11600565, 3203078,
    11591776, 3946495, 8389632]
    ![8388800, 412495, 12012772, 8389696, 8805145, 3212427, 3211395, 1333513, 10844335,
    1342076, 3211267, 8390508, 12964289, 2187778, 10577327, 15826947, 11601678, 11917580,
    16472861, 3212989, 10772033, 9789060, 5097123, 8419304] hf hy hc (by decide +kernel)
  exact monsterCo1GeometryTransport_matrix_line_products
    monsterCo1GeometryVectorPoint16Transport monsterCo1GeometryVectorPoint30Transport 6
    monsterCo1GeometryVectorPoint16Matrix monsterCo1GeometryVectorPoint16InverseMatrix
    monsterCo1GeometryVectorPoint30Matrix
    monsterCo1GeometryVectorPoint66AfterSignMatrix
    monsterCo1GeometryVectorPoint66AfterInverseMatrix monsterCo1GeometryVectorPoint66Matrix
    monsterCo1GeometryVectorPoint16Transport_binary
    monsterCo1GeometryVectorPoint16Transport_inverse_binary
    monsterCo1GeometryVectorPoint30Transport_binary
    hc1 hc2 hc3 v

/-- Source point 66 is the literal actual transported frame point. -/
def monsterCo1GeometryVectorPoint66 : MonsterCo1GeometryPoint :=
  monsterCo1GeometryVectorPoint66Transport • monsterCo1GeometryBasePoint

/-- Complete binary coordinates of this literal actual source point. -/
theorem monsterCo1GeometryVectorPoint66_binary :
    monsterCo1GeometryVectorPoint66.val =
      ![0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0] := by
  change co1BinaryAction monsterCo1GeometryVectorPoint66Transport monsterCo1GeometryBasePoint.val =
      _
  rw [monsterCo1GeometryVectorPoint66Transport_binary, monsterCo1GeometryBasePoint_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
