/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Original-coordinate candidate data for preferred octad basis twenty. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsRemainingOctadInverseBasis
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortInverseU
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsMixedPacketNorm
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonUOrderData

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Complete original-coordinate ForwardOctadChoice data for the mixed candidate. -/
def monsterNortonCodeTwentyForwardOctadChoice : Fin 8 → Fin 94 :=
  ![15, 16, 17, 18, 27, 28, 64, 65]

/-- Complete original-coordinate ForwardSign data for the mixed candidate. -/
def monsterNortonCodeTwentyForwardSign : Fin 8 → Fin 32 → Fin 64 :=
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
def monsterNortonCodeTwentyForwardShortCoefficient : Fin 8 → Fin 32 → ℤ :=
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
def monsterNortonCodeTwentyForwardSpinLabel : Fin 16 → Fin 4096 :=
  ![1105, 1107, 1117, 1119, 1281, 1283, 1293, 1295,
    3153, 3155, 3165, 3167, 3329, 3331, 3341, 3343]

/-- Complete original-coordinate ForwardSpinCoefficient data for the mixed candidate. -/
def monsterNortonCodeTwentyForwardSpinCoefficient : Fin 16 → ℤ :=
  ![2, 2, 2, 2, -2, -2, -2, -2,
    -2, -2, -2, -2, 2, 2, 2, 2]

/-- Complete original-coordinate ForwardColumns data for the mixed candidate. -/
def monsterNortonCodeTwentyForwardColumns : Fin 4 → Fin 24 :=
  ![16, 19, 20, 22]

/-- Complete original-coordinate ForwardLeech data for the mixed candidate. -/
def monsterNortonCodeTwentyForwardLeech : Fin 24 → ℤ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    2, 0, 0, -2, 2, 0, -2, 0]

/-- Complete original-coordinate InverseOctadChoice data for the mixed candidate. -/
def monsterNortonCodeTwentyInverseOctadChoice : Fin 8 → Fin 76 :=
  ![4, 9, 17, 22, 40, 49, 60, 67]

/-- Complete original-coordinate InverseSign data for the mixed candidate. -/
def monsterNortonCodeTwentyInverseSign : Fin 8 → Fin 32 → Fin 64 :=
  ![![0, 1, 2, 3, 12, 13, 14, 15,
    16, 17, 18, 19, 28, 29, 30, 31,
    36, 37, 38, 39, 40, 41, 42, 43,
    52, 53, 54, 55, 56, 57, 58, 59],
  ![0, 3, 4, 7, 8, 11, 12, 15,
    16, 19, 20, 23, 24, 27, 28, 31,
    33, 34, 37, 38, 41, 42, 45, 46,
    49, 50, 53, 54, 57, 58, 61, 62],
  ![0, 3, 4, 7, 8, 11, 12, 15,
    16, 19, 20, 23, 24, 27, 28, 31,
    33, 34, 37, 38, 41, 42, 45, 46,
    49, 50, 53, 54, 57, 58, 61, 62],
  ![0, 3, 4, 7, 8, 11, 12, 15,
    17, 18, 21, 22, 25, 26, 29, 30,
    32, 35, 36, 39, 40, 43, 44, 47,
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
def monsterNortonCodeTwentyInverseShortCoefficient : Fin 8 → Fin 32 → ℤ :=
  ![![3, -3, -3, -3, 1, -1, -1, -1,
    -3, -3, -3, 3, -1, -1, -1, 1,
    1, -1, -1, -1, 1, -1, -1, -1,
    -1, -1, -1, 1, -1, -1, -1, 1],
  ![-3, 3, -1, 1, -1, 1, -1, 1,
    -1, 1, -1, 1, -1, 1, -3, 3,
    3, 3, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 3, 3],
  ![-1, 1, 1, -1, 1, -1, 1, -1,
    1, -1, 1, -1, 1, -1, -1, 1,
    1, 1, -1, -1, -1, -1, -1, -1,
    -1, -1, -1, -1, -1, -1, 1, 1],
  ![1, -1, -1, 1, -1, 1, -1, 1,
    -1, -1, 1, 1, 1, 1, 1, 1,
    -1, 1, -1, 1, -1, 1, 1, -1,
    1, 1, 1, 1, 1, 1, -1, -1],
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
def monsterNortonCodeTwentyInverseSpinLabel : Fin 16 → Fin 4096 :=
  ![28, 64, 284, 320, 1053, 1089, 1309, 1345,
    2076, 2112, 2332, 2368, 3101, 3137, 3357, 3393]

/-- Complete original-coordinate InverseSpinCoefficient data for the mixed candidate. -/
def monsterNortonCodeTwentyInverseSpinCoefficient : Fin 16 → ℤ :=
  ![-2, 2, -2, 2, 2, -2, 2, -2,
    2, -2, 2, -2, -2, 2, -2, 2]

/-- Complete original-coordinate InverseColumns data for the mixed candidate. -/
def monsterNortonCodeTwentyInverseColumns : Fin 4 → Fin 24 :=
  ![14, 15, 17, 21]

/-- Complete original-coordinate InverseLeech data for the mixed candidate. -/
def monsterNortonCodeTwentyInverseLeech : Fin 24 → ℤ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 2, 2,
    0, 2, 0, 0, 0, 2, 0, 0]

/-- The full integer squared norm is exactly 512. -/
theorem monsterNortonCodeTwenty_forward_short_sq :
    (∑ i : Fin 8, ∑ j : Fin 32, monsterNortonCodeTwentyForwardShortCoefficient i j ^ 2) = 512 := by
  decide +kernel

/-- The full integer squared norm is exactly 512. -/
theorem monsterNortonCodeTwenty_inverse_short_sq :
    (∑ i : Fin 8, ∑ j : Fin 32, monsterNortonCodeTwentyInverseShortCoefficient i j ^ 2) = 512 := by
  decide +kernel

/-- The full integer squared norm is exactly 64. -/
theorem monsterNortonCodeTwenty_forward_spin_sq :
    (∑ i : Fin 16, monsterNortonCodeTwentyForwardSpinCoefficient i ^ 2) = 64 := by
  decide +kernel

/-- The full integer squared norm is exactly 64. -/
theorem monsterNortonCodeTwenty_inverse_spin_sq :
    (∑ i : Fin 16, monsterNortonCodeTwentyInverseSpinCoefficient i ^ 2) = 64 := by
  decide +kernel

/-- The full integer squared norm is exactly 16. -/
theorem monsterNortonCodeTwenty_forward_leech_sq :
    (∑ i : Fin 24, monsterNortonCodeTwentyForwardLeech i ^ 2) = 16 := by
  decide +kernel

/-- The full integer squared norm is exactly 16. -/
theorem monsterNortonCodeTwenty_inverse_leech_sq :
    (∑ i : Fin 24, monsterNortonCodeTwentyInverseLeech i ^ 2) = 16 := by
  decide +kernel

/-- The entire physical candidate is transported by the actual Norton numerator. -/
theorem monsterNortonCodeTwenty_leech_certificate (j : Fin 24) :
    (∑ i : Fin 24, monsterNortonUNumerator1 j i * monsterNortonCodeTwentyForwardLeech i) =
      4 * monsterNortonCodeTwentyInverseLeech j := by
  revert j
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
