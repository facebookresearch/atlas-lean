/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Original-coordinate candidate data for preferred octad basis twentyone. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsRemainingOctadInverseBasis
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortInverseU
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsMixedPacketNorm
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonUOrderData

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Complete original-coordinate ForwardOctadChoice data for the mixed candidate. -/
def monsterNortonCodeTwentyOneForwardOctadChoice : Fin 8 → Fin 94 :=
  ![23, 24, 25, 26, 37, 38, 74, 75]

/-- Complete original-coordinate ForwardSign data for the mixed candidate. -/
def monsterNortonCodeTwentyOneForwardSign : Fin 8 → Fin 32 → Fin 64 :=
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
def monsterNortonCodeTwentyOneForwardShortCoefficient : Fin 8 → Fin 32 → ℤ :=
  ![![1, -1, 1, 1, 1, 1, -1, 1,
    -1, 1, -1, -1, -1, -1, 1, -1,
    -1, 1, -1, -1, -1, -1, 1, -1,
    -1, 1, -1, -1, -1, -1, 1, -1],
  ![-1, -1, -1, 1, 1, -1, -1, -1,
    -3, -3, -3, 3, 3, -3, -3, -3,
    -1, -1, -1, 1, 1, -1, -1, -1,
    -1, -1, -1, 1, 1, -1, -1, -1],
  ![-1, 1, -1, -1, -1, -1, 1, -1,
    -3, 3, -3, -3, -3, -3, 3, -3,
    -1, 1, -1, -1, -1, -1, 1, -1,
    -1, 1, -1, -1, -1, -1, 1, -1],
  ![1, 1, 1, -1, -1, 1, 1, 1,
    -1, -1, -1, 1, 1, -1, -1, -1,
    -1, -1, -1, 1, 1, -1, -1, -1,
    -1, -1, -1, 1, 1, -1, -1, -1],
  ![1, -1, -1, -1, -1, -1, -1, 1,
    -1, 1, 1, 1, 1, 1, 1, -1,
    -1, 1, 1, 1, 1, 1, 1, -1,
    -1, 1, 1, 1, 1, 1, 1, -1],
  ![-1, 1, 1, 1, 1, 1, 1, -1,
    -3, 3, 3, 3, 3, 3, 3, -3,
    -1, 1, 1, 1, 1, 1, 1, -1,
    -1, 1, 1, 1, 1, 1, 1, -1],
  ![1, 1, -1, 1, 1, -1, 1, 1,
    -1, -1, 1, -1, -1, 1, -1, -1,
    -1, -1, 1, -1, -1, 1, -1, -1,
    -1, -1, 1, -1, -1, 1, -1, -1],
  ![-1, -1, 1, -1, -1, 1, -1, -1,
    -3, -3, 3, -3, -3, 3, -3, -3,
    -1, -1, 1, -1, -1, 1, -1, -1,
    -1, -1, 1, -1, -1, 1, -1, -1]]

/-- Complete original-coordinate ForwardSpinLabel data for the mixed candidate. -/
def monsterNortonCodeTwentyOneForwardSpinLabel : Fin 16 → Fin 4096 :=
  ![1185, 1187, 1197, 1199, 1537, 1539, 1549, 1551,
    3233, 3235, 3245, 3247, 3585, 3587, 3597, 3599]

/-- Complete original-coordinate ForwardSpinCoefficient data for the mixed candidate. -/
def monsterNortonCodeTwentyOneForwardSpinCoefficient : Fin 16 → ℤ :=
  ![2, 2, 2, 2, -2, -2, -2, -2,
    -2, -2, -2, -2, 2, 2, 2, 2]

/-- Complete original-coordinate ForwardColumns data for the mixed candidate. -/
def monsterNortonCodeTwentyOneForwardColumns : Fin 4 → Fin 24 :=
  ![16, 17, 20, 23]

/-- Complete original-coordinate ForwardLeech data for the mixed candidate. -/
def monsterNortonCodeTwentyOneForwardLeech : Fin 24 → ℤ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    2, -2, 0, 0, 2, 0, 0, -2]

/-- Complete original-coordinate InverseOctadChoice data for the mixed candidate. -/
def monsterNortonCodeTwentyOneInverseOctadChoice : Fin 8 → Fin 76 :=
  ![3, 10, 16, 23, 37, 46, 63, 70]

/-- Complete original-coordinate InverseSign data for the mixed candidate. -/
def monsterNortonCodeTwentyOneInverseSign : Fin 8 → Fin 32 → Fin 64 :=
  ![![0, 1, 2, 3, 12, 13, 14, 15,
    20, 21, 22, 23, 24, 25, 26, 27,
    32, 33, 34, 35, 44, 45, 46, 47,
    52, 53, 54, 55, 56, 57, 58, 59],
  ![0, 1, 2, 3, 12, 13, 14, 15,
    16, 17, 18, 19, 28, 29, 30, 31,
    36, 37, 38, 39, 40, 41, 42, 43,
    52, 53, 54, 55, 56, 57, 58, 59],
  ![0, 1, 2, 3, 12, 13, 14, 15,
    16, 17, 18, 19, 28, 29, 30, 31,
    36, 37, 38, 39, 40, 41, 42, 43,
    52, 53, 54, 55, 56, 57, 58, 59],
  ![0, 3, 4, 7, 8, 11, 12, 15,
    16, 19, 20, 23, 24, 27, 28, 31,
    33, 34, 37, 38, 41, 42, 45, 46,
    49, 50, 53, 54, 57, 58, 61, 62],
  ![0, 2, 4, 6, 9, 11, 13, 15,
    17, 19, 21, 23, 24, 26, 28, 30,
    33, 35, 37, 39, 40, 42, 44, 46,
    48, 50, 52, 54, 57, 59, 61, 63],
  ![0, 3, 5, 6, 9, 10, 12, 15,
    16, 19, 21, 22, 25, 26, 28, 31,
    32, 35, 37, 38, 41, 42, 44, 47,
    48, 51, 53, 54, 57, 58, 60, 63],
  ![0, 3, 5, 6, 9, 10, 12, 15,
    16, 19, 21, 22, 25, 26, 28, 31,
    32, 35, 37, 38, 41, 42, 44, 47,
    48, 51, 53, 54, 57, 58, 60, 63],
  ![0, 2, 4, 6, 9, 11, 13, 15,
    17, 19, 21, 23, 24, 26, 28, 30,
    33, 35, 37, 39, 40, 42, 44, 46,
    48, 50, 52, 54, 57, 59, 61, 63]]

/-- Complete original-coordinate InverseShortCoefficient data for the mixed candidate. -/
def monsterNortonCodeTwentyOneInverseShortCoefficient : Fin 8 → Fin 32 → ℤ :=
  ![![-3, 3, 3, 3, -1, 1, 1, 1,
    -1, 1, 1, 1, -1, 1, 1, 1,
    3, 3, 3, -3, 1, 1, 1, -1,
    1, 1, 1, -1, 1, 1, 1, -1],
  ![3, -3, -3, -3, 1, -1, -1, -1,
    -3, -3, -3, 3, -1, -1, -1, 1,
    1, -1, -1, -1, 1, -1, -1, -1,
    -1, -1, -1, 1, -1, -1, -1, 1],
  ![1, -1, -1, -1, -1, 1, 1, 1,
    -1, -1, -1, 1, 1, 1, 1, -1,
    -1, 1, 1, 1, -1, 1, 1, 1,
    1, 1, 1, -1, 1, 1, 1, -1],
  ![-1, 1, 1, -1, 1, -1, 1, -1,
    1, -1, 1, -1, 1, -1, -1, 1,
    1, 1, -1, -1, -1, -1, -1, -1,
    -1, -1, -1, -1, -1, -1, 1, 1],
  ![-1, 1, 1, 1, 1, -1, -1, -1,
    1, -1, -1, -1, 1, -1, -1, -1,
    1, -1, -1, -1, 1, -1, -1, -1,
    1, -1, -1, -1, -1, 1, 1, 1],
  ![3, -3, -3, -3, -3, -3, -3, 3,
    1, -1, -1, -1, -1, -1, -1, 1,
    1, -1, -1, -1, -1, -1, -1, 1,
    1, -1, -1, -1, -1, -1, -1, 1],
  ![3, -3, -3, -3, -3, -3, -3, 3,
    1, -1, -1, -1, -1, -1, -1, 1,
    1, -1, -1, -1, -1, -1, -1, 1,
    1, -1, -1, -1, -1, -1, -1, 1],
  ![-1, 1, 1, 1, 1, -1, -1, -1,
    1, -1, -1, -1, 1, -1, -1, -1,
    1, -1, -1, -1, 1, -1, -1, -1,
    1, -1, -1, -1, -1, 1, 1, 1]]

/-- Complete original-coordinate InverseSpinLabel data for the mixed candidate. -/
def monsterNortonCodeTwentyOneInverseSpinLabel : Fin 16 → Fin 4096 :=
  ![16, 76, 272, 332, 1055, 1091, 1311, 1347,
    2064, 2124, 2320, 2380, 3103, 3139, 3359, 3395]

/-- Complete original-coordinate InverseSpinCoefficient data for the mixed candidate. -/
def monsterNortonCodeTwentyOneInverseSpinCoefficient : Fin 16 → ℤ :=
  ![2, -2, 2, -2, -2, 2, -2, 2,
    -2, 2, -2, 2, 2, -2, 2, -2]

/-- Complete original-coordinate InverseColumns data for the mixed candidate. -/
def monsterNortonCodeTwentyOneInverseColumns : Fin 4 → Fin 24 :=
  ![14, 15, 18, 23]

/-- Complete original-coordinate InverseLeech data for the mixed candidate. -/
def monsterNortonCodeTwentyOneInverseLeech : Fin 24 → ℤ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 2, 2,
    0, 0, 2, 0, 0, 0, 0, 2]

/-- The full integer squared norm is exactly 512. -/
theorem monsterNortonCodeTwentyOne_forward_short_sq :
    (∑ i : Fin 8, ∑ j : Fin 32, monsterNortonCodeTwentyOneForwardShortCoefficient i j ^ 2) =
      512 := by
  decide +kernel

/-- The full integer squared norm is exactly 512. -/
theorem monsterNortonCodeTwentyOne_inverse_short_sq :
    (∑ i : Fin 8, ∑ j : Fin 32, monsterNortonCodeTwentyOneInverseShortCoefficient i j ^ 2) =
      512 := by
  decide +kernel

/-- The full integer squared norm is exactly 64. -/
theorem monsterNortonCodeTwentyOne_forward_spin_sq :
    (∑ i : Fin 16, monsterNortonCodeTwentyOneForwardSpinCoefficient i ^ 2) = 64 := by
  decide +kernel

/-- The full integer squared norm is exactly 64. -/
theorem monsterNortonCodeTwentyOne_inverse_spin_sq :
    (∑ i : Fin 16, monsterNortonCodeTwentyOneInverseSpinCoefficient i ^ 2) = 64 := by
  decide +kernel

/-- The full integer squared norm is exactly 16. -/
theorem monsterNortonCodeTwentyOne_forward_leech_sq :
    (∑ i : Fin 24, monsterNortonCodeTwentyOneForwardLeech i ^ 2) = 16 := by
  decide +kernel

/-- The full integer squared norm is exactly 16. -/
theorem monsterNortonCodeTwentyOne_inverse_leech_sq :
    (∑ i : Fin 24, monsterNortonCodeTwentyOneInverseLeech i ^ 2) = 16 := by
  decide +kernel

/-- The entire physical candidate is transported by the actual Norton numerator. -/
theorem monsterNortonCodeTwentyOne_leech_certificate (j : Fin 24) :
    (∑ i : Fin 24, monsterNortonUNumerator1 j i * monsterNortonCodeTwentyOneForwardLeech i) =
      4 * monsterNortonCodeTwentyOneInverseLeech j := by
  revert j
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
