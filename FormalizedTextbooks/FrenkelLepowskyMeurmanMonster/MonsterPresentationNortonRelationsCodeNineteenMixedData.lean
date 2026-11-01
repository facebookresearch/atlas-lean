/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Original-coordinate candidate data for preferred octad basis nineteen. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsRemainingOctadInverseBasis
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortInverseU
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsMixedPacketNorm
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonUOrderData

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Complete original-coordinate ForwardOctadChoice data for the mixed candidate. -/
def monsterNortonCodeNineteenForwardOctadChoice : Fin 8 → Fin 94 :=
  ![19, 20, 21, 22, 39, 40, 76, 77]

/-- Complete original-coordinate ForwardSign data for the mixed candidate. -/
def monsterNortonCodeNineteenForwardSign : Fin 8 → Fin 32 → Fin 64 :=
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
def monsterNortonCodeNineteenForwardShortCoefficient : Fin 8 → Fin 32 → ℤ :=
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
def monsterNortonCodeNineteenForwardSpinLabel : Fin 16 → Fin 4096 :=
  ![1152, 1153, 1164, 1165, 1568, 1569, 1580, 1581,
    3200, 3201, 3212, 3213, 3616, 3617, 3628, 3629]

/-- Complete original-coordinate ForwardSpinCoefficient data for the mixed candidate. -/
def monsterNortonCodeNineteenForwardSpinCoefficient : Fin 16 → ℤ :=
  ![2, -2, 2, -2, -2, 2, -2, 2,
    -2, 2, -2, 2, 2, -2, 2, -2]

/-- Complete original-coordinate ForwardColumns data for the mixed candidate. -/
def monsterNortonCodeNineteenForwardColumns : Fin 4 → Fin 24 :=
  ![16, 19, 20, 21]

/-- Complete original-coordinate ForwardLeech data for the mixed candidate. -/
def monsterNortonCodeNineteenForwardLeech : Fin 24 → ℤ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    2, 0, 0, -2, 2, -2, 0, 0]

/-- Complete original-coordinate InverseOctadChoice data for the mixed candidate. -/
def monsterNortonCodeNineteenInverseOctadChoice : Fin 8 → Fin 76 :=
  ![5, 14, 18, 31, 38, 47, 65, 74]

/-- Complete original-coordinate InverseSign data for the mixed candidate. -/
def monsterNortonCodeNineteenInverseSign : Fin 8 → Fin 32 → Fin 64 :=
  ![![0, 3, 5, 6, 8, 11, 13, 14,
    16, 19, 21, 22, 24, 27, 29, 30,
    33, 34, 36, 39, 41, 42, 44, 47,
    49, 50, 52, 55, 57, 58, 60, 63],
  ![0, 3, 5, 6, 8, 11, 13, 14,
    17, 18, 20, 23, 25, 26, 28, 31,
    32, 35, 37, 38, 40, 43, 45, 46,
    49, 50, 52, 55, 57, 58, 60, 63],
  ![0, 1, 2, 3, 12, 13, 14, 15,
    20, 21, 22, 23, 24, 25, 26, 27,
    32, 33, 34, 35, 44, 45, 46, 47,
    52, 53, 54, 55, 56, 57, 58, 59],
  ![0, 3, 4, 7, 8, 11, 12, 15,
    16, 19, 20, 23, 24, 27, 28, 31,
    33, 34, 37, 38, 41, 42, 45, 46,
    49, 50, 53, 54, 57, 58, 61, 62],
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
def monsterNortonCodeNineteenInverseShortCoefficient : Fin 8 → Fin 32 → ℤ :=
  ![![-3, 3, 3, 3, -1, 1, 1, 1,
    -1, 1, 1, 1, -1, 1, 1, 1,
    3, 3, 3, -3, 1, 1, 1, -1,
    1, 1, 1, -1, 1, 1, 1, -1],
  ![3, -3, -3, -3, 1, -1, -1, -1,
    -3, -3, -3, 3, -1, -1, -1, 1,
    1, -1, -1, -1, 1, -1, -1, -1,
    -1, -1, -1, 1, -1, -1, -1, 1],
  ![1, -1, -1, -1, -1, 1, 1, 1,
    -1, 1, 1, 1, -1, 1, 1, 1,
    -1, -1, -1, 1, 1, 1, 1, -1,
    1, 1, 1, -1, 1, 1, 1, -1],
  ![-1, 1, 1, -1, 1, -1, 1, -1,
    1, -1, 1, -1, 1, -1, -1, 1,
    1, 1, -1, -1, -1, -1, -1, -1,
    -1, -1, -1, -1, -1, -1, 1, 1],
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
def monsterNortonCodeNineteenInverseSpinLabel : Fin 16 → Fin 4096 :=
  ![32, 198, 288, 454, 1071, 1225, 1327, 1481,
    2080, 2246, 2336, 2502, 3119, 3273, 3375, 3529]

/-- Complete original-coordinate InverseSpinCoefficient data for the mixed candidate. -/
def monsterNortonCodeNineteenInverseSpinCoefficient : Fin 16 → ℤ :=
  ![2, -2, 2, -2, -2, 2, -2, 2,
    -2, 2, -2, 2, 2, -2, 2, -2]

/-- Complete original-coordinate InverseColumns data for the mixed candidate. -/
def monsterNortonCodeNineteenInverseColumns : Fin 4 → Fin 24 :=
  ![15, 17, 21, 23]

/-- Complete original-coordinate InverseLeech data for the mixed candidate. -/
def monsterNortonCodeNineteenInverseLeech : Fin 24 → ℤ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 2,
    0, 2, 0, 0, 0, 2, 0, 2]

/-- The full integer squared norm is exactly 512. -/
theorem monsterNortonCodeNineteen_forward_short_sq :
    (∑ i : Fin 8, ∑ j : Fin 32, monsterNortonCodeNineteenForwardShortCoefficient i j ^ 2) =
      512 := by
  decide +kernel

/-- The full integer squared norm is exactly 512. -/
theorem monsterNortonCodeNineteen_inverse_short_sq :
    (∑ i : Fin 8, ∑ j : Fin 32, monsterNortonCodeNineteenInverseShortCoefficient i j ^ 2) =
      512 := by
  decide +kernel

/-- The full integer squared norm is exactly 64. -/
theorem monsterNortonCodeNineteen_forward_spin_sq :
    (∑ i : Fin 16, monsterNortonCodeNineteenForwardSpinCoefficient i ^ 2) = 64 := by
  decide +kernel

/-- The full integer squared norm is exactly 64. -/
theorem monsterNortonCodeNineteen_inverse_spin_sq :
    (∑ i : Fin 16, monsterNortonCodeNineteenInverseSpinCoefficient i ^ 2) = 64 := by
  decide +kernel

/-- The full integer squared norm is exactly 16. -/
theorem monsterNortonCodeNineteen_forward_leech_sq :
    (∑ i : Fin 24, monsterNortonCodeNineteenForwardLeech i ^ 2) = 16 := by
  decide +kernel

/-- The full integer squared norm is exactly 16. -/
theorem monsterNortonCodeNineteen_inverse_leech_sq :
    (∑ i : Fin 24, monsterNortonCodeNineteenInverseLeech i ^ 2) = 16 := by
  decide +kernel

/-- The entire physical candidate is transported by the actual Norton numerator. -/
theorem monsterNortonCodeNineteen_leech_certificate (j : Fin 24) :
    (∑ i : Fin 24, monsterNortonUNumerator1 j i * monsterNortonCodeNineteenForwardLeech i) =
      4 * monsterNortonCodeNineteenInverseLeech j := by
  revert j
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
