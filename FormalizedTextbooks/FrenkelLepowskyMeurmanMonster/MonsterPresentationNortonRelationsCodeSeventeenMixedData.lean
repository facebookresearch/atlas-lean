/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Original-coordinate candidate data for preferred octad basis seventeen. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsRemainingOctadInverseBasis
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortInverseU
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsMixedPacketNorm
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonUOrderData

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Complete original-coordinate ForwardOctadChoice data for the mixed candidate. -/
def monsterNortonCodeSeventeenForwardOctadChoice : Fin 8 → Fin 94 :=
  ![7, 8, 9, 10, 41, 42, 78, 79]

/-- Complete original-coordinate ForwardSign data for the mixed candidate. -/
def monsterNortonCodeSeventeenForwardSign : Fin 8 → Fin 32 → Fin 64 :=
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
def monsterNortonCodeSeventeenForwardShortCoefficient : Fin 8 → Fin 32 → ℤ :=
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
def monsterNortonCodeSeventeenForwardSpinLabel : Fin 16 → Fin 4096 :=
  ![1056, 1059, 1068, 1071, 1664, 1667, 1676, 1679,
    3104, 3107, 3116, 3119, 3712, 3715, 3724, 3727]

/-- Complete original-coordinate ForwardSpinCoefficient data for the mixed candidate. -/
def monsterNortonCodeSeventeenForwardSpinCoefficient : Fin 16 → ℤ :=
  ![2, -2, 2, -2, -2, 2, -2, 2,
    -2, 2, -2, 2, 2, -2, 2, -2]

/-- Complete original-coordinate ForwardColumns data for the mixed candidate. -/
def monsterNortonCodeSeventeenForwardColumns : Fin 4 → Fin 24 :=
  ![16, 18, 20, 22]

/-- Complete original-coordinate ForwardLeech data for the mixed candidate. -/
def monsterNortonCodeSeventeenForwardLeech : Fin 24 → ℤ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    2, 0, -2, 0, 2, 0, -2, 0]

/-- Complete original-coordinate InverseOctadChoice data for the mixed candidate. -/
def monsterNortonCodeSeventeenInverseOctadChoice : Fin 8 → Fin 76 :=
  ![7, 12, 20, 27, 39, 48, 64, 72]

/-- Complete original-coordinate InverseSign data for the mixed candidate. -/
def monsterNortonCodeSeventeenInverseSign : Fin 8 → Fin 32 → Fin 64 :=
  ![![0, 3, 5, 6, 8, 11, 13, 14,
    16, 19, 21, 22, 24, 27, 29, 30,
    32, 35, 37, 38, 40, 43, 45, 46,
    48, 51, 53, 54, 56, 59, 61, 62],
  ![0, 1, 2, 3, 4, 5, 6, 7,
    24, 25, 26, 27, 28, 29, 30, 31,
    40, 41, 42, 43, 44, 45, 46, 47,
    48, 49, 50, 51, 52, 53, 54, 55],
  ![0, 3, 4, 7, 8, 11, 12, 15,
    16, 19, 20, 23, 24, 27, 28, 31,
    33, 34, 37, 38, 41, 42, 45, 46,
    49, 50, 53, 54, 57, 58, 61, 62],
  ![0, 3, 4, 7, 8, 11, 12, 15,
    16, 19, 20, 23, 24, 27, 28, 31,
    33, 34, 37, 38, 41, 42, 45, 46,
    49, 50, 53, 54, 57, 58, 61, 62],
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
def monsterNortonCodeSeventeenInverseShortCoefficient : Fin 8 → Fin 32 → ℤ :=
  ![![-3, 3, 3, 3, -1, 1, 1, 1,
    -1, 1, 1, 1, -1, 1, 1, 1,
    -1, 1, 1, 1, -1, 1, 1, 1,
    -1, 1, 1, 1, -3, 3, 3, 3],
  ![3, -3, -3, -3, -3, -3, -3, 3,
    1, -1, -1, -1, -1, -1, -1, 1,
    1, -1, -1, -1, -1, -1, -1, 1,
    1, -1, -1, -1, -1, -1, -1, 1],
  ![1, -1, -1, 1, -1, 1, -1, 1,
    -1, 1, -1, 1, -1, 1, 1, -1,
    -1, -1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, -1, -1],
  ![-1, 1, 1, -1, 1, -1, 1, -1,
    1, -1, 1, -1, 1, -1, -1, 1,
    1, 1, -1, -1, -1, -1, -1, -1,
    -1, -1, -1, -1, -1, -1, 1, 1],
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
def monsterNortonCodeSeventeenInverseSpinLabel : Fin 16 → Fin 4096 :=
  ![48, 138, 304, 394, 1087, 1157, 1343, 1413,
    2096, 2186, 2352, 2442, 3135, 3205, 3391, 3461]

/-- Complete original-coordinate InverseSpinCoefficient data for the mixed candidate. -/
def monsterNortonCodeSeventeenInverseSpinCoefficient : Fin 16 → ℤ :=
  ![2, -2, 2, -2, -2, 2, -2, 2,
    -2, 2, -2, 2, 2, -2, 2, -2]

/-- Complete original-coordinate InverseColumns data for the mixed candidate. -/
def monsterNortonCodeSeventeenInverseColumns : Fin 4 → Fin 24 :=
  ![14, 17, 18, 21]

/-- Complete original-coordinate InverseLeech data for the mixed candidate. -/
def monsterNortonCodeSeventeenInverseLeech : Fin 24 → ℤ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 2, 0,
    0, 2, 2, 0, 0, 2, 0, 0]

/-- The full integer squared norm is exactly 512. -/
theorem monsterNortonCodeSeventeen_forward_short_sq :
    (∑ i : Fin 8, ∑ j : Fin 32, monsterNortonCodeSeventeenForwardShortCoefficient i j ^ 2) =
      512 := by
  decide +kernel

/-- The full integer squared norm is exactly 512. -/
theorem monsterNortonCodeSeventeen_inverse_short_sq :
    (∑ i : Fin 8, ∑ j : Fin 32, monsterNortonCodeSeventeenInverseShortCoefficient i j ^ 2) =
      512 := by
  decide +kernel

/-- The full integer squared norm is exactly 64. -/
theorem monsterNortonCodeSeventeen_forward_spin_sq :
    (∑ i : Fin 16, monsterNortonCodeSeventeenForwardSpinCoefficient i ^ 2) = 64 := by
  decide +kernel

/-- The full integer squared norm is exactly 64. -/
theorem monsterNortonCodeSeventeen_inverse_spin_sq :
    (∑ i : Fin 16, monsterNortonCodeSeventeenInverseSpinCoefficient i ^ 2) = 64 := by
  decide +kernel

/-- The full integer squared norm is exactly 16. -/
theorem monsterNortonCodeSeventeen_forward_leech_sq :
    (∑ i : Fin 24, monsterNortonCodeSeventeenForwardLeech i ^ 2) = 16 := by
  decide +kernel

/-- The full integer squared norm is exactly 16. -/
theorem monsterNortonCodeSeventeen_inverse_leech_sq :
    (∑ i : Fin 24, monsterNortonCodeSeventeenInverseLeech i ^ 2) = 16 := by
  decide +kernel

/-- The entire physical candidate is transported by the actual Norton numerator. -/
theorem monsterNortonCodeSeventeen_leech_certificate (j : Fin 24) :
    (∑ i : Fin 24, monsterNortonUNumerator1 j i * monsterNortonCodeSeventeenForwardLeech i) =
      4 * monsterNortonCodeSeventeenInverseLeech j := by
  revert j
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
