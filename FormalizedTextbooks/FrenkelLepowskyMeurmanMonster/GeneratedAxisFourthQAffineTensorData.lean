/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthOddCoefficients

/-! Exact pairing and original signs for the fourth axis's 56 Y tensor states. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The actual spatial coordinate of each paired affine state. -/
def generatedFourthQAffineTensorColumns : Fin 28 → Fin 24 :=
  ![0, 1, 2, 3, 8, 8, 8, 8,
    8, 8, 11, 11, 11, 11, 11, 11,
    12, 13, 14, 15, 16, 17, 18, 19,
    20, 21, 22, 23]

/-- The low dictionary base label of each paired affine state. -/
def generatedFourthQAffineTensorBaseLabels : Fin 28 → Fin 2048 :=
  ![1333, 1329, 1331, 1335, 1024, 1028, 1540, 1542,
    1794, 1796, 1024, 1028, 1540, 1542, 1794, 1796,
    1591, 1587, 1585, 1589, 1073, 1079, 1075, 1077,
    1843, 1841, 1847, 1845]

/-- The character label of each paired affine state. -/
def generatedFourthQAffineTensorCharacterLabels : Fin 28 → Fin 4096 :=
  ![2048, 2048, 2048, 2048, 2050, 2050, 2050, 2050,
    2050, 2050, 2050, 2050, 2050, 2050, 2050, 2050,
    2048, 2048, 2048, 2048, 2048, 2048, 2048, 2048,
    2048, 2048, 2048, 2048]

/-- The original whole-state sign, recorded as a binary phase. -/
def generatedFourthQAffineTensorScalePhases : Fin 28 → ZMod 2 :=
  ![1, 0, 0, 0, 1, 0, 0, 1,
    1, 1, 0, 1, 1, 0, 0, 0,
    1, 1, 1, 0, 1, 1, 1, 0,
    0, 0, 0, 1]

/-- The exact 56-term dictionary permutation, in pairs. -/
def generatedFourthQAffineTensorPairRows : Fin 28 → Fin 56 × Fin 56 :=
  ![(29, 28), (27, 26), (52, 53), (50, 51), (14, 15), (12, 13), (20, 21), (23, 22),
    (16, 17), (18, 19), (3, 2), (1, 0), (9, 8), (10, 11), (5, 4), (7, 6),
    (33, 32), (38, 39), (41, 40), (46, 47), (42, 43), (34, 35), (36, 37), (44, 45),
    (55, 54), (25, 24), (48, 49), (30, 31)]

/-- Repeated column-eleven states map to their column-eight family. -/
def generatedFourthQAffineTensorFamilyIndex : Fin 28 → Fin 22 :=
  ![0, 1, 2, 3, 4, 5, 6, 7,
    8, 9, 4, 5, 6, 7, 8, 9,
    10, 11, 12, 13, 14, 15, 16, 17,
    18, 19, 20, 21]

/-- The literal reindexing of all 56 actual signed Y tensor terms. -/
def generatedFourthQAffineTensorPairIndex (x : Fin 28 × Fin 2) : Fin 56 :=
  if x.2 = 0 then (generatedFourthQAffineTensorPairRows x.1).1
    else (generatedFourthQAffineTensorPairRows x.1).2

/-- Every actual signed tensor term is paired exactly once. -/
theorem generatedFourthQAffineTensorPairIndex_bijective :
    Function.Bijective generatedFourthQAffineTensorPairIndex := by
  decide +kernel

/-- Each first dictionary label is the actual low affine base in its spatial column. -/
theorem generatedFourthQAffineTensor_first_output : ∀ k : Fin 28,
    generatedFourthOddRootOutputData (generatedFourthQAffineTensorPairIndex (k, 0)) =
      (generatedFourthQAffineTensorBaseLabels k, generatedFourthQAffineTensorColumns k) := by
  decide +kernel

/-- The second dictionary label differs by the actual common low plane vector. -/
theorem generatedFourthQAffineTensor_second_output : ∀ k : Fin 28,
    golayLabelCoefficients
        ⟨(generatedFourthOddRootOutputData
          (generatedFourthQAffineTensorPairIndex (k, 1))).1.val, by omega⟩ =
      golayLabelCoefficients ⟨(generatedFourthQAffineTensorBaseLabels k).val, by omega⟩ +
        golayLabelCoefficients 14 ∧
    (generatedFourthOddRootOutputData
      (generatedFourthQAffineTensorPairIndex (k, 1))).2 =
        generatedFourthQAffineTensorColumns k := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
-- The kernel checks 56 original mask signs and their twelve-coordinate character values.
/-- The genuine original short phases and Y-mask phases give the displayed affine signs. -/
theorem generatedFourthQAffineTensor_sign_certificate : ∀ k : Fin 28, ∀ s : Fin 2,
    generatedFourthOddCoefficientPhaseData (generatedFourthQAffineTensorPairIndex (k, s)) +
      golayBooleanCast ((golayEncodedMask (generatedFourthOddRootOutputData
        (generatedFourthQAffineTensorPairIndex (k, s))).1.val).testBit
          (generatedFourthQAffineTensorColumns k).val) =
    generatedFourthQAffineTensorScalePhases k +
      (s.val : ZMod 2) * spinDot
        (golayLabelCoefficients (generatedFourthQAffineTensorCharacterLabels k))
        (golayLabelCoefficients 14) := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
