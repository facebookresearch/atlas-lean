/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Original-coordinate candidate data for preferred octad basis sixteen. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsRemainingOctadInverseBasis
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortInverseU
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsMixedPacketNorm
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonUOrderData

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Complete original-coordinate ForwardOctadChoice data for the mixed candidate. -/
def monsterNortonCodeSixteenForwardOctadChoice : Fin 8 → Fin 94 :=
  ![3, 4, 5, 6, 31, 32, 68, 69]

/-- Complete original-coordinate ForwardSign data for the mixed candidate. -/
def monsterNortonCodeSixteenForwardSign : Fin 8 → Fin 32 → Fin 64 :=
  ![![0, 3, 5, 6, 9, 10, 12, 15,
    16, 19, 21, 22, 25, 26, 28, 31,
    32, 35, 37, 38, 41, 42, 44, 47,
    48, 51, 53, 54, 57, 58, 60, 63],
  ![0, 3, 5, 6, 9, 10, 12, 15,
    16, 19, 21, 22, 25, 26, 28, 31,
    32, 35, 37, 38, 41, 42, 44, 47,
    48, 51, 53, 54, 57, 58, 60, 63],
  ![0, 3, 5, 6, 9, 10, 12, 15,
    16, 19, 21, 22, 25, 26, 28, 31,
    32, 35, 37, 38, 41, 42, 44, 47,
    48, 51, 53, 54, 57, 58, 60, 63],
  ![0, 3, 5, 6, 9, 10, 12, 15,
    16, 19, 21, 22, 25, 26, 28, 31,
    32, 35, 37, 38, 41, 42, 44, 47,
    48, 51, 53, 54, 57, 58, 60, 63],
  ![0, 3, 5, 6, 9, 10, 12, 15,
    16, 19, 21, 22, 25, 26, 28, 31,
    32, 35, 37, 38, 41, 42, 44, 47,
    48, 51, 53, 54, 57, 58, 60, 63],
  ![0, 3, 5, 6, 9, 10, 12, 15,
    16, 19, 21, 22, 25, 26, 28, 31,
    32, 35, 37, 38, 41, 42, 44, 47,
    48, 51, 53, 54, 57, 58, 60, 63],
  ![0, 3, 5, 6, 9, 10, 12, 15,
    16, 19, 21, 22, 25, 26, 28, 31,
    32, 35, 37, 38, 41, 42, 44, 47,
    48, 51, 53, 54, 57, 58, 60, 63],
  ![0, 3, 5, 6, 9, 10, 12, 15,
    16, 19, 21, 22, 25, 26, 28, 31,
    32, 35, 37, 38, 41, 42, 44, 47,
    48, 51, 53, 54, 57, 58, 60, 63]]

/-- Complete original-coordinate ForwardShortCoefficient data for the mixed candidate. -/
def monsterNortonCodeSixteenForwardShortCoefficient : Fin 8 → Fin 32 → ℤ :=
  ![![1, -1, -1, -1, -1, -1, -1, 1,
    -1, 1, 1, 1, 1, 1, 1, -1,
    -1, 1, 1, 1, 1, 1, 1, -1,
    -1, 1, 1, 1, 1, 1, 1, -1],
  ![1, 1, -1, 1, 1, -1, 1, 1,
    -1, -1, 1, -1, -1, 1, -1, -1,
    -1, -1, 1, -1, -1, 1, -1, -1,
    -1, -1, 1, -1, -1, 1, -1, -1],
  ![-1, 1, 1, 1, 1, 1, 1, -1,
    -3, 3, 3, 3, 3, 3, 3, -3,
    -1, 1, 1, 1, 1, 1, 1, -1,
    -1, 1, 1, 1, 1, 1, 1, -1],
  ![-1, -1, 1, -1, -1, 1, -1, -1,
    -3, -3, 3, -3, -3, 3, -3, -3,
    -1, -1, 1, -1, -1, 1, -1, -1,
    -1, -1, 1, -1, -1, 1, -1, -1],
  ![1, -1, 1, 1, 1, 1, -1, 1,
    -1, 1, -1, -1, -1, -1, 1, -1,
    -1, 1, -1, -1, -1, -1, 1, -1,
    -1, 1, -1, -1, -1, -1, 1, -1],
  ![-1, 1, -1, -1, -1, -1, 1, -1,
    -3, 3, -3, -3, -3, -3, 3, -3,
    -1, 1, -1, -1, -1, -1, 1, -1,
    -1, 1, -1, -1, -1, -1, 1, -1],
  ![-1, -1, -1, 1, 1, -1, -1, -1,
    -3, -3, -3, 3, 3, -3, -3, -3,
    -1, -1, -1, 1, 1, -1, -1, -1,
    -1, -1, -1, 1, 1, -1, -1, -1],
  ![1, 1, 1, -1, -1, 1, 1, 1,
    -1, -1, -1, 1, 1, -1, -1, -1,
    -1, -1, -1, 1, 1, -1, -1, -1,
    -1, -1, -1, 1, 1, -1, -1, -1]]

/-- Complete original-coordinate ForwardSpinLabel data for the mixed candidate. -/
def monsterNortonCodeSixteenForwardSpinLabel : Fin 16 → Fin 4096 :=
  ![1040, 1043, 1052, 1055, 1344, 1347, 1356, 1359,
    3088, 3091, 3100, 3103, 3392, 3395, 3404, 3407]

/-- Complete original-coordinate ForwardSpinCoefficient data for the mixed candidate. -/
def monsterNortonCodeSixteenForwardSpinCoefficient : Fin 16 → ℤ :=
  ![2, -2, 2, -2, -2, 2, -2, 2,
    -2, 2, -2, 2, 2, -2, 2, -2]

/-- Complete original-coordinate ForwardColumns data for the mixed candidate. -/
def monsterNortonCodeSixteenForwardColumns : Fin 4 → Fin 24 :=
  ![16, 17, 20, 21]

/-- Complete original-coordinate ForwardLeech data for the mixed candidate. -/
def monsterNortonCodeSixteenForwardLeech : Fin 24 → ℤ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    2, -2, 0, 0, 2, -2, 0, 0]

/-- Complete original-coordinate InverseOctadChoice data for the mixed candidate. -/
def monsterNortonCodeSixteenInverseOctadChoice : Fin 8 → Fin 76 :=
  ![8, 11, 21, 26, 42, 50, 62, 69]

/-- Complete original-coordinate InverseSign data for the mixed candidate. -/
def monsterNortonCodeSixteenInverseSign : Fin 8 → Fin 32 → Fin 64 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7,
    24, 25, 26, 27, 28, 29, 30, 31,
    40, 41, 42, 43, 44, 45, 46, 47,
    48, 49, 50, 51, 52, 53, 54, 55],
  ![0, 1, 2, 3, 4, 5, 6, 7,
    24, 25, 26, 27, 28, 29, 30, 31,
    40, 41, 42, 43, 44, 45, 46, 47,
    48, 49, 50, 51, 52, 53, 54, 55],
  ![0, 3, 4, 7, 8, 11, 12, 15,
    16, 19, 20, 23, 24, 27, 28, 31,
    33, 34, 37, 38, 41, 42, 45, 46,
    49, 50, 53, 54, 57, 58, 61, 62],
  ![0, 1, 2, 3, 12, 13, 14, 15,
    20, 21, 22, 23, 24, 25, 26, 27,
    32, 33, 34, 35, 44, 45, 46, 47,
    52, 53, 54, 55, 56, 57, 58, 59],
  ![0, 1, 6, 7, 8, 9, 14, 15,
    16, 17, 22, 23, 24, 25, 30, 31,
    34, 35, 36, 37, 42, 43, 44, 45,
    50, 51, 52, 53, 58, 59, 60, 61],
  ![0, 1, 2, 3, 4, 5, 6, 7,
    24, 25, 26, 27, 28, 29, 30, 31,
    40, 41, 42, 43, 44, 45, 46, 47,
    48, 49, 50, 51, 52, 53, 54, 55],
  ![0, 3, 5, 6, 8, 11, 13, 14,
    17, 18, 20, 23, 25, 26, 28, 31,
    32, 35, 37, 38, 40, 43, 45, 46,
    49, 50, 52, 55, 57, 58, 60, 63],
  ![0, 1, 6, 7, 8, 9, 14, 15,
    16, 17, 22, 23, 24, 25, 30, 31,
    34, 35, 36, 37, 42, 43, 44, 45,
    50, 51, 52, 53, 58, 59, 60, 61]]

/-- Complete original-coordinate InverseShortCoefficient data for the mixed candidate. -/
def monsterNortonCodeSixteenInverseShortCoefficient : Fin 8 → Fin 32 → ℤ :=
  ![![3, -3, -3, -3, -3, -3, -3, 3,
    1, -1, -1, -1, -1, -1, -1, 1,
    1, -1, -1, -1, -1, -1, -1, 1,
    1, -1, -1, -1, -1, -1, -1, 1],
  ![-3, 3, 3, 3, 3, 3, 3, -3,
    -1, 1, 1, 1, 1, 1, 1, -1,
    -1, 1, 1, 1, 1, 1, 1, -1,
    -1, 1, 1, 1, 1, 1, 1, -1],
  ![-1, 1, 1, -1, 1, -1, 1, -1,
    1, -1, 1, -1, 1, -1, -1, 1,
    1, 1, -1, -1, -1, -1, -1, -1,
    -1, -1, -1, -1, -1, -1, 1, 1],
  ![1, -1, -1, -1, -1, 1, 1, 1,
    -1, 1, 1, 1, -1, 1, 1, 1,
    -1, -1, -1, 1, 1, 1, 1, -1,
    1, 1, 1, -1, 1, 1, 1, -1],
  ![-1, 1, 1, -1, 1, 1, -1, -1,
    1, 1, -1, -1, 1, -1, -1, 1,
    1, -1, 1, -1, -1, -1, -1, -1,
    -1, -1, -1, -1, -1, 1, -1, 1],
  ![3, -3, -3, -3, -3, -3, -3, 3,
    1, -1, -1, -1, -1, -1, -1, 1,
    1, -1, -1, -1, -1, -1, -1, 1,
    1, -1, -1, -1, -1, -1, -1, 1],
  ![3, -3, -3, -3, 1, -1, -1, -1,
    -3, -3, -3, 3, -1, -1, -1, 1,
    1, -1, -1, -1, 1, -1, -1, -1,
    -1, -1, -1, 1, -1, -1, -1, 1],
  ![-1, 1, 1, -1, 1, 1, -1, -1,
    1, 1, -1, -1, 1, -1, -1, 1,
    1, -1, 1, -1, -1, -1, -1, -1,
    -1, -1, -1, -1, -1, 1, -1, 1]]

/-- Complete original-coordinate InverseSpinLabel data for the mixed candidate. -/
def monsterNortonCodeSixteenInverseSpinLabel : Fin 16 → Fin 4096 :=
  ![58, 128, 314, 384, 1083, 1153, 1339, 1409,
    2106, 2176, 2362, 2432, 3131, 3201, 3387, 3457]

/-- Complete original-coordinate InverseSpinCoefficient data for the mixed candidate. -/
def monsterNortonCodeSixteenInverseSpinCoefficient : Fin 16 → ℤ :=
  ![-2, 2, -2, 2, 2, -2, 2, -2,
    2, -2, 2, -2, -2, 2, -2, 2]

/-- Complete original-coordinate InverseColumns data for the mixed candidate. -/
def monsterNortonCodeSixteenInverseColumns : Fin 4 → Fin 24 :=
  ![15, 17, 18, 23]

/-- Complete original-coordinate InverseLeech data for the mixed candidate. -/
def monsterNortonCodeSixteenInverseLeech : Fin 24 → ℤ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 2,
    0, 2, 2, 0, 0, 0, 0, 2]

/-- The full integer squared norm is exactly 512. -/
theorem monsterNortonCodeSixteen_forward_short_sq :
    (∑ i : Fin 8, ∑ j : Fin 32, monsterNortonCodeSixteenForwardShortCoefficient i j ^ 2) = 512 := by
  decide +kernel

/-- The full integer squared norm is exactly 512. -/
theorem monsterNortonCodeSixteen_inverse_short_sq :
    (∑ i : Fin 8, ∑ j : Fin 32, monsterNortonCodeSixteenInverseShortCoefficient i j ^ 2) = 512 := by
  decide +kernel

/-- The full integer squared norm is exactly 64. -/
theorem monsterNortonCodeSixteen_forward_spin_sq :
    (∑ i : Fin 16, monsterNortonCodeSixteenForwardSpinCoefficient i ^ 2) = 64 := by
  decide +kernel

/-- The full integer squared norm is exactly 64. -/
theorem monsterNortonCodeSixteen_inverse_spin_sq :
    (∑ i : Fin 16, monsterNortonCodeSixteenInverseSpinCoefficient i ^ 2) = 64 := by
  decide +kernel

/-- The full integer squared norm is exactly 16. -/
theorem monsterNortonCodeSixteen_forward_leech_sq :
    (∑ i : Fin 24, monsterNortonCodeSixteenForwardLeech i ^ 2) = 16 := by
  decide +kernel

/-- The full integer squared norm is exactly 16. -/
theorem monsterNortonCodeSixteen_inverse_leech_sq :
    (∑ i : Fin 24, monsterNortonCodeSixteenInverseLeech i ^ 2) = 16 := by
  decide +kernel

/-- The entire physical candidate is transported by the actual Norton numerator. -/
theorem monsterNortonCodeSixteen_leech_certificate (j : Fin 24) :
    (∑ i : Fin 24, monsterNortonUNumerator1 j i * monsterNortonCodeSixteenForwardLeech i) =
      4 * monsterNortonCodeSixteenInverseLeech j := by
  revert j
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
