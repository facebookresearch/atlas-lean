/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Original-coordinate candidate data for preferred octad basis eighteen. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsRemainingOctadInverseBasis
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortInverseU
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsMixedPacketNorm
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonUOrderData

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Complete original-coordinate ForwardOctadChoice data for the mixed candidate. -/
def monsterNortonCodeEighteenForwardOctadChoice : Fin 8 → Fin 94 :=
  ![11, 12, 13, 14, 29, 30, 66, 67]

/-- Complete original-coordinate ForwardSign data for the mixed candidate. -/
def monsterNortonCodeEighteenForwardSign : Fin 8 → Fin 32 → Fin 64 :=
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
def monsterNortonCodeEighteenForwardShortCoefficient : Fin 8 → Fin 32 → ℤ :=
  ![![1, -1, -1, -1, -1, -1, -1, 1,
    -1, 1, 1, 1, 1, 1, 1, -1,
    -1, 1, 1, 1, 1, 1, 1, -1,
    -1, 1, 1, 1, 1, 1, 1, -1],
  ![-1, -1, 1, -1, -1, 1, -1, -1,
    -3, -3, 3, -3, -3, 3, -3, -3,
    -1, -1, 1, -1, -1, 1, -1, -1,
    -1, -1, 1, -1, -1, 1, -1, -1],
  ![-1, 1, 1, 1, 1, 1, 1, -1,
    -3, 3, 3, 3, 3, 3, 3, -3,
    -1, 1, 1, 1, 1, 1, 1, -1,
    -1, 1, 1, 1, 1, 1, 1, -1],
  ![1, 1, -1, 1, 1, -1, 1, 1,
    -1, -1, 1, -1, -1, 1, -1, -1,
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
  ![1, 1, 1, -1, -1, 1, 1, 1,
    -1, -1, -1, 1, 1, -1, -1, -1,
    -1, -1, -1, 1, 1, -1, -1, -1,
    -1, -1, -1, 1, 1, -1, -1, -1],
  ![-1, -1, -1, 1, 1, -1, -1, -1,
    -3, -3, -3, 3, 3, -3, -3, -3,
    -1, -1, -1, 1, 1, -1, -1, -1,
    -1, -1, -1, 1, 1, -1, -1, -1]]

/-- Complete original-coordinate ForwardSpinLabel data for the mixed candidate. -/
def monsterNortonCodeEighteenForwardSpinLabel : Fin 16 → Fin 4096 :=
  ![1088, 1089, 1100, 1101, 1296, 1297, 1308, 1309,
    3136, 3137, 3148, 3149, 3344, 3345, 3356, 3357]

/-- Complete original-coordinate ForwardSpinCoefficient data for the mixed candidate. -/
def monsterNortonCodeEighteenForwardSpinCoefficient : Fin 16 → ℤ :=
  ![2, -2, 2, -2, -2, 2, -2, 2,
    -2, 2, -2, 2, 2, -2, 2, -2]

/-- Complete original-coordinate ForwardColumns data for the mixed candidate. -/
def monsterNortonCodeEighteenForwardColumns : Fin 4 → Fin 24 :=
  ![16, 18, 20, 23]

/-- Complete original-coordinate ForwardLeech data for the mixed candidate. -/
def monsterNortonCodeEighteenForwardLeech : Fin 24 → ℤ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    2, 0, -2, 0, 2, 0, 0, -2]

/-- Complete original-coordinate InverseOctadChoice data for the mixed candidate. -/
def monsterNortonCodeEighteenInverseOctadChoice : Fin 8 → Fin 76 :=
  ![6, 13, 19, 30, 44, 51, 61, 68]

/-- Complete original-coordinate InverseSign data for the mixed candidate. -/
def monsterNortonCodeEighteenInverseSign : Fin 8 → Fin 32 → Fin 64 :=
  ![![0, 3, 5, 6, 8, 11, 13, 14,
    17, 18, 20, 23, 25, 26, 28, 31,
    32, 35, 37, 38, 40, 43, 45, 46,
    49, 50, 52, 55, 57, 58, 60, 63],
  ![0, 3, 5, 6, 8, 11, 13, 14,
    16, 19, 21, 22, 24, 27, 29, 30,
    33, 34, 36, 39, 41, 42, 44, 47,
    49, 50, 52, 55, 57, 58, 60, 63],
  ![0, 3, 4, 7, 8, 11, 12, 15,
    16, 19, 20, 23, 24, 27, 28, 31,
    33, 34, 37, 38, 41, 42, 45, 46,
    49, 50, 53, 54, 57, 58, 61, 62],
  ![0, 1, 2, 3, 12, 13, 14, 15,
    20, 21, 22, 23, 24, 25, 26, 27,
    32, 33, 34, 35, 44, 45, 46, 47,
    52, 53, 54, 55, 56, 57, 58, 59],
  ![0, 2, 4, 6, 9, 11, 13, 15,
    17, 19, 21, 23, 24, 26, 28, 30,
    32, 34, 36, 38, 41, 43, 45, 47,
    49, 51, 53, 55, 56, 58, 60, 62],
  ![0, 1, 2, 3, 4, 5, 6, 7,
    24, 25, 26, 27, 28, 29, 30, 31,
    40, 41, 42, 43, 44, 45, 46, 47,
    48, 49, 50, 51, 52, 53, 54, 55],
  ![0, 3, 5, 6, 8, 11, 13, 14,
    16, 19, 21, 22, 24, 27, 29, 30,
    33, 34, 36, 39, 41, 42, 44, 47,
    49, 50, 52, 55, 57, 58, 60, 63],
  ![0, 2, 4, 6, 9, 11, 13, 15,
    17, 19, 21, 23, 24, 26, 28, 30,
    32, 34, 36, 38, 41, 43, 45, 47,
    49, 51, 53, 55, 56, 58, 60, 62]]

/-- Complete original-coordinate InverseShortCoefficient data for the mixed candidate. -/
def monsterNortonCodeEighteenInverseShortCoefficient : Fin 8 → Fin 32 → ℤ :=
  ![![3, -3, -3, -3, 1, -1, -1, -1,
    -3, -3, -3, 3, -1, -1, -1, 1,
    1, -1, -1, -1, 1, -1, -1, -1,
    -1, -1, -1, 1, -1, -1, -1, 1],
  ![-3, 3, 3, 3, -1, 1, 1, 1,
    -1, 1, 1, 1, -1, 1, 1, 1,
    3, 3, 3, -3, 1, 1, 1, -1,
    1, 1, 1, -1, 1, 1, 1, -1],
  ![-1, 1, 1, -1, 1, -1, 1, -1,
    1, -1, 1, -1, 1, -1, -1, 1,
    1, 1, -1, -1, -1, -1, -1, -1,
    -1, -1, -1, -1, -1, -1, 1, 1],
  ![1, -1, -1, -1, -1, 1, 1, 1,
    -1, 1, 1, 1, -1, 1, 1, 1,
    -1, -1, -1, 1, 1, 1, 1, -1,
    1, 1, 1, -1, 1, 1, 1, -1],
  ![-1, 1, 1, 1, 1, -1, -1, -1,
    1, -1, -1, -1, 1, -1, -1, -1,
    1, 1, 1, -1, -1, -1, -1, 1,
    -1, -1, -1, 1, -1, -1, -1, 1],
  ![3, -3, -3, -3, -3, -3, -3, 3,
    1, -1, -1, -1, -1, -1, -1, 1,
    1, -1, -1, -1, -1, -1, -1, 1,
    1, -1, -1, -1, -1, -1, -1, 1],
  ![3, -3, -3, -3, 1, -1, -1, -1,
    1, -1, -1, -1, 1, -1, -1, -1,
    -3, -3, -3, 3, -1, -1, -1, 1,
    -1, -1, -1, 1, -1, -1, -1, 1],
  ![-1, 1, 1, 1, 1, -1, -1, -1,
    1, -1, -1, -1, 1, -1, -1, -1,
    1, 1, 1, -1, -1, -1, -1, 1,
    -1, -1, -1, 1, -1, -1, -1, 1]]

/-- Complete original-coordinate InverseSpinLabel data for the mixed candidate. -/
def monsterNortonCodeEighteenInverseSpinLabel : Fin 16 → Fin 4096 :=
  ![38, 192, 294, 448, 1063, 1217, 1319, 1473,
    2086, 2240, 2342, 2496, 3111, 3265, 3367, 3521]

/-- Complete original-coordinate InverseSpinCoefficient data for the mixed candidate. -/
def monsterNortonCodeEighteenInverseSpinCoefficient : Fin 16 → ℤ :=
  ![-2, 2, -2, 2, 2, -2, 2, -2,
    2, -2, 2, -2, -2, 2, -2, 2]

/-- Complete original-coordinate InverseColumns data for the mixed candidate. -/
def monsterNortonCodeEighteenInverseColumns : Fin 4 → Fin 24 :=
  ![14, 18, 21, 23]

/-- Complete original-coordinate InverseLeech data for the mixed candidate. -/
def monsterNortonCodeEighteenInverseLeech : Fin 24 → ℤ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 2, 0,
    0, 0, 2, 0, 0, 2, 0, 2]

/-- The full integer squared norm is exactly 512. -/
theorem monsterNortonCodeEighteen_forward_short_sq :
    (∑ i : Fin 8, ∑ j : Fin 32, monsterNortonCodeEighteenForwardShortCoefficient i j ^ 2) =
      512 := by
  decide +kernel

/-- The full integer squared norm is exactly 512. -/
theorem monsterNortonCodeEighteen_inverse_short_sq :
    (∑ i : Fin 8, ∑ j : Fin 32, monsterNortonCodeEighteenInverseShortCoefficient i j ^ 2) =
      512 := by
  decide +kernel

/-- The full integer squared norm is exactly 64. -/
theorem monsterNortonCodeEighteen_forward_spin_sq :
    (∑ i : Fin 16, monsterNortonCodeEighteenForwardSpinCoefficient i ^ 2) = 64 := by
  decide +kernel

/-- The full integer squared norm is exactly 64. -/
theorem monsterNortonCodeEighteen_inverse_spin_sq :
    (∑ i : Fin 16, monsterNortonCodeEighteenInverseSpinCoefficient i ^ 2) = 64 := by
  decide +kernel

/-- The full integer squared norm is exactly 16. -/
theorem monsterNortonCodeEighteen_forward_leech_sq :
    (∑ i : Fin 24, monsterNortonCodeEighteenForwardLeech i ^ 2) = 16 := by
  decide +kernel

/-- The full integer squared norm is exactly 16. -/
theorem monsterNortonCodeEighteen_inverse_leech_sq :
    (∑ i : Fin 24, monsterNortonCodeEighteenInverseLeech i ^ 2) = 16 := by
  decide +kernel

/-- The entire physical candidate is transported by the actual Norton numerator. -/
theorem monsterNortonCodeEighteen_leech_certificate (j : Fin 24) :
    (∑ i : Fin 24, monsterNortonUNumerator1 j i * monsterNortonCodeEighteenForwardLeech i) =
      4 * monsterNortonCodeEighteenInverseLeech j := by
  revert j
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
