/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Complete actual-coordinate candidate data for preferred pair basis ten. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortPairsInverseSixth
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsMixedPacketNorm
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonUOrderData

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Complete original-coordinate ForwardOddCodes data for preferred basis ten. -/
def monsterNortonCodeTenForwardOddCodes : Fin 32 → Fin 2048 :=
  ![1024, 1025, 1026, 1027, 1036, 1037, 1038, 1039,
    1360, 1361, 1362, 1363, 1372, 1373, 1374, 1375,
    1696, 1697, 1698, 1699, 1708, 1709, 1710, 1711,
    2032, 2033, 2034, 2035, 2044, 2045, 2046, 2047]

/-- Complete original-coordinate ForwardColumns data for preferred basis ten. -/
def monsterNortonCodeTenForwardColumns : Fin 8 → Fin 24 :=
  ![16, 17, 18, 19, 20, 21, 22, 23]

/-- Complete original-coordinate ForwardShortCoefficient data for preferred basis ten. -/
def monsterNortonCodeTenForwardShortCoefficient : Fin 32 → Fin 8 → ℤ :=
  ![![-3, -1, -1, -1, 1, -1, -1, -1],
  ![3, 1, 1, 1, -1, 1, 1, 1],
  ![3, 1, 1, 1, -1, 1, 1, 1],
  ![3, 1, 1, 1, -1, 1, 1, 1],
  ![-3, -1, -1, -1, 1, -1, -1, -1],
  ![3, 1, 1, 1, -1, 1, 1, 1],
  ![3, 1, 1, 1, -1, 1, 1, 1],
  ![3, 1, 1, 1, -1, 1, 1, 1],
  ![3, 1, 1, 1, -1, 1, 1, 1],
  ![-3, -1, -1, -1, 1, -1, -1, -1],
  ![-3, -1, -1, -1, 1, -1, -1, -1],
  ![-3, -1, -1, -1, 1, -1, -1, -1],
  ![3, 1, 1, 1, -1, 1, 1, 1],
  ![-3, -1, -1, -1, 1, -1, -1, -1],
  ![-3, -1, -1, -1, 1, -1, -1, -1],
  ![-3, -1, -1, -1, 1, -1, -1, -1],
  ![3, 1, 1, 1, -1, 1, 1, 1],
  ![-3, -1, -1, -1, 1, -1, -1, -1],
  ![-3, -1, -1, -1, 1, -1, -1, -1],
  ![-3, -1, -1, -1, 1, -1, -1, -1],
  ![3, 1, 1, 1, -1, 1, 1, 1],
  ![-3, -1, -1, -1, 1, -1, -1, -1],
  ![-3, -1, -1, -1, 1, -1, -1, -1],
  ![-3, -1, -1, -1, 1, -1, -1, -1],
  ![3, 1, 1, 1, -1, 1, 1, 1],
  ![-3, -1, -1, -1, 1, -1, -1, -1],
  ![-3, -1, -1, -1, 1, -1, -1, -1],
  ![-3, -1, -1, -1, 1, -1, -1, -1],
  ![3, 1, 1, 1, -1, 1, 1, 1],
  ![-3, -1, -1, -1, 1, -1, -1, -1],
  ![-3, -1, -1, -1, 1, -1, -1, -1],
  ![-3, -1, -1, -1, 1, -1, -1, -1]]

/-- Complete original-coordinate ForwardSpinLabel data for preferred basis ten. -/
def monsterNortonCodeTenForwardSpinLabel : Fin 64 → Fin 4096 :=
  ![0, 1, 2, 3, 12, 13, 14, 15,
    336, 337, 338, 339, 348, 349, 350, 351,
    672, 673, 674, 675, 684, 685, 686, 687,
    1008, 1009, 1010, 1011, 1020, 1021, 1022, 1023,
    2048, 2049, 2050, 2051, 2060, 2061, 2062, 2063,
    2384, 2385, 2386, 2387, 2396, 2397, 2398, 2399,
    2720, 2721, 2722, 2723, 2732, 2733, 2734, 2735,
    3056, 3057, 3058, 3059, 3068, 3069, 3070, 3071]

/-- Complete original-coordinate ForwardSpinCoefficient data for preferred basis ten. -/
def monsterNortonCodeTenForwardSpinCoefficient : Fin 64 → ℤ :=
  ![1, -1, -1, 1, -1, 1, 1, -1,
    1, -1, -1, 1, -1, 1, 1, -1,
    1, -1, -1, 1, -1, 1, 1, -1,
    1, -1, -1, 1, -1, 1, 1, -1,
    1, -1, -1, 1, -1, 1, 1, -1,
    1, -1, -1, 1, -1, 1, 1, -1,
    1, -1, -1, 1, -1, 1, 1, -1,
    1, -1, -1, 1, -1, 1, 1, -1]

/-- Complete original-coordinate ForwardLeech data for preferred basis ten. -/
def monsterNortonCodeTenForwardLeech : Fin 24 → ℤ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    3, 1, 1, 1, -1, 1, 1, 1]

/-- Actual first physical coordinates of the inverse pair support. -/
def monsterNortonCodeTenInversePairFirst : Fin 128 → Fin 24 :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    1, 1, 1, 1, 1, 1, 1, 1,
    2, 2, 2, 2, 2, 2, 2, 2,
    2, 2, 2, 2, 2, 2, 3, 3,
    3, 3, 3, 3, 3, 3, 3, 3,
    3, 3, 3, 3, 4, 4, 4, 4,
    4, 4, 5, 5, 5, 5, 5, 5,
    6, 6, 6, 6, 6, 6, 7, 7,
    7, 7, 7, 7, 8, 8, 8, 8,
    8, 8, 9, 9, 9, 9, 9, 9,
    10, 10, 10, 10, 10, 10, 11, 11,
    11, 11, 11, 11, 12, 12, 12, 12,
    12, 12, 13, 13, 13, 13, 13, 13,
    14, 14, 14, 14, 15, 15, 15, 15,
    16, 16, 16, 16, 17, 17, 17, 18,
    18, 18, 19, 19, 20, 20, 21, 22]

/-- Actual second physical coordinates of the inverse pair support. -/
def monsterNortonCodeTenInversePairSecond : Fin 128 → Fin 24 :=
  ![2, 3, 14, 15, 17, 18, 21, 23,
    2, 3, 14, 15, 17, 18, 21, 23,
    4, 5, 6, 7, 8, 9, 10, 11,
    12, 13, 16, 19, 20, 22, 4, 5,
    6, 7, 8, 9, 10, 11, 12, 13,
    16, 19, 20, 22, 14, 15, 17, 18,
    21, 23, 14, 15, 17, 18, 21, 23,
    14, 15, 17, 18, 21, 23, 14, 15,
    17, 18, 21, 23, 14, 15, 17, 18,
    21, 23, 14, 15, 17, 18, 21, 23,
    14, 15, 17, 18, 21, 23, 14, 15,
    17, 18, 21, 23, 14, 15, 17, 18,
    21, 23, 14, 15, 17, 18, 21, 23,
    16, 19, 20, 22, 16, 19, 20, 22,
    17, 18, 21, 23, 19, 20, 22, 19,
    20, 22, 21, 23, 21, 23, 22, 23]

/-- Every inverse supported pair is represented in increasing physical order. -/
theorem monsterNortonCodeTenInversePair_lt (i : Fin 128) :
    monsterNortonCodeTenInversePairFirst i < monsterNortonCodeTenInversePairSecond i := by
  revert i
  decide +kernel

/-- The actual coordinate-model index of each supported inverse physical pair. -/
noncomputable def monsterNortonCodeTenInversePair (i : Fin 128) : Fin 276 :=
  griessPairIndex (monsterNortonCodeTenInversePairFirst i)
    (monsterNortonCodeTenInversePairSecond i) (ne_of_lt (monsterNortonCodeTenInversePair_lt i))

/-- Distinct inverse support entries give distinct increasing physical pairs. -/
theorem monsterNortonCodeTenInversePairPhysical_injective :
    Function.Injective (fun i =>
      (monsterNortonCodeTenInversePairFirst i, monsterNortonCodeTenInversePairSecond i)) := by
  decide +kernel

/-- Complete original-coordinate InverseShortCoefficient data for preferred basis ten. -/
def monsterNortonCodeTenInverseShortCoefficient : Fin 2 → Fin 128 → ℤ :=
  ![![-1, 3, -1, -1, -1, -1, -1, -1,
    -1, 3, -1, -1, -1, -1, -1, -1,
    1, 1, -1, -1, 1, 1, -1, -1,
    -1, -1, 1, 1, 1, 1, -3, -3,
    3, 3, -3, -3, 3, 3, 3, 3,
    -3, -3, -3, -3, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1,
    -1, -1, -1, -1, -1, -1, -1, -1,
    -1, -1, -1, -1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1,
    -1, -1, -1, -1, -1, -1, -1, -1,
    -1, -1, -1, -1, -1, -1, -1, -1,
    -1, -1, -1, -1, -1, -1, -1, -1,
    1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1],
  ![1, -3, 1, 1, 1, 1, 1, 1,
    1, -3, 1, 1, 1, 1, 1, 1,
    -1, -1, 1, 1, -1, -1, 1, 1,
    1, 1, -1, -1, -1, -1, 3, 3,
    -3, -3, 3, 3, -3, -3, -3, -3,
    3, 3, 3, 3, -1, -1, -1, -1,
    -1, -1, -1, -1, -1, -1, -1, -1,
    1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, -1, -1, -1, -1,
    -1, -1, -1, -1, -1, -1, -1, -1,
    1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1,
    -1, -1, -1, -1, -1, -1, -1, -1,
    -1, -1, -1, -1, -1, -1, -1, -1,
    -1, -1, -1, -1, -1, -1, -1, -1]]

/-- Complete original-coordinate InverseSpinLabel data for preferred basis ten. -/
def monsterNortonCodeTenInverseSpinLabel : Fin 4 → Fin 4096 :=
  ![82, 338, 2130, 2386]

/-- Complete original-coordinate InverseSpinCoefficient data for preferred basis ten. -/
def monsterNortonCodeTenInverseSpinCoefficient : Fin 4 → ℤ :=
  ![4, -4, -4, 4]

/-- Complete original-coordinate InverseColumns data for preferred basis ten. -/
def monsterNortonCodeTenInverseColumns : Fin 1 → Fin 24 :=
  ![3]

/-- Complete original-coordinate InverseLeech data for preferred basis ten. -/
def monsterNortonCodeTenInverseLeech : Fin 24 → ℤ :=
  ![0, 0, 0, -4, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0]

/-- The full integer squared norm is exactly 512. -/
theorem monsterNortonCodeTen_forward_short_sq :
    (∑ i : Fin 32, ∑ j : Fin 8, monsterNortonCodeTenForwardShortCoefficient i j ^ 2) = 512 := by
  decide +kernel

/-- The full integer squared norm is exactly 512. -/
theorem monsterNortonCodeTen_inverse_short_sq :
    (∑ i : Fin 2, ∑ j : Fin 128, monsterNortonCodeTenInverseShortCoefficient i j ^ 2) = 512 := by
  decide +kernel

/-- The full integer squared norm is exactly 64. -/
theorem monsterNortonCodeTen_forward_spin_sq :
    (∑ i : Fin 64, monsterNortonCodeTenForwardSpinCoefficient i ^ 2) = 64 := by
  decide +kernel

/-- The full integer squared norm is exactly 64. -/
theorem monsterNortonCodeTen_inverse_spin_sq :
    (∑ i : Fin 4, monsterNortonCodeTenInverseSpinCoefficient i ^ 2) = 64 := by
  decide +kernel

/-- The full integer squared norm is exactly 16. -/
theorem monsterNortonCodeTen_forward_leech_sq :
    (∑ i : Fin 24, monsterNortonCodeTenForwardLeech i ^ 2) = 16 := by
  decide +kernel

/-- The full integer squared norm is exactly 16. -/
theorem monsterNortonCodeTen_inverse_leech_sq :
    (∑ i : Fin 24, monsterNortonCodeTenInverseLeech i ^ 2) = 16 := by
  decide +kernel

/-- The entire physical factor follows the actual Norton matrix numerator. -/
theorem monsterNortonCodeTen_leech_certificate (j : Fin 24) :
    (∑ i : Fin 24, monsterNortonUNumerator1 j i * monsterNortonCodeTenForwardLeech i) =
      4 * monsterNortonCodeTenInverseLeech j := by
  revert j
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
