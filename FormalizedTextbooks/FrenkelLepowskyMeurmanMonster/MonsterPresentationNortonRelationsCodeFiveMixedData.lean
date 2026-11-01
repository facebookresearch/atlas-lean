/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Original-coordinate candidate data for the code-five mixed forward and inverse packets. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsRemainingOctadInverseBasis
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsMixedPacketNorm
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonUOrderData

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- Original odd source codes in the forward candidate. -/
def monsterNortonCodeFiveForwardOddCodes : Fin 32 → Fin 2048 :=
  ![1028, 1029, 1030, 1031, 1032, 1033, 1034, 1035,
  1364, 1365, 1366, 1367, 1368, 1369, 1370, 1371,
  1700, 1701, 1702, 1703, 1704, 1705, 1706, 1707,
  2036, 2037, 2038, 2039, 2040, 2041, 2042, 2043]

/-- Original physical columns in the forward short candidate. -/
def monsterNortonCodeFiveForwardColumns : Fin 8 → Fin 24 :=
  ![16, 17, 18, 19, 20, 21, 22, 23]

/-- Integer short coefficients before division by thirty-two. -/
def monsterNortonCodeFiveForwardShortCoefficient : Fin 32 → Fin 8 → ℤ :=
  ![![-3, -1, -1, -1, 1, -1, -1, -1],
![-3, -1, -1, -1, 1, -1, -1, -1],
![3, 1, 1, 1, -1, 1, 1, 1],
![-3, -1, -1, -1, 1, -1, -1, -1],
![3, 1, 1, 1, -1, 1, 1, 1],
![3, 1, 1, 1, -1, 1, 1, 1],
![-3, -1, -1, -1, 1, -1, -1, -1],
![3, 1, 1, 1, -1, 1, 1, 1],
![-3, -1, -1, -1, 1, -1, -1, -1],
![-3, -1, -1, -1, 1, -1, -1, -1],
![3, 1, 1, 1, -1, 1, 1, 1],
![-3, -1, -1, -1, 1, -1, -1, -1],
![3, 1, 1, 1, -1, 1, 1, 1],
![3, 1, 1, 1, -1, 1, 1, 1],
![-3, -1, -1, -1, 1, -1, -1, -1],
![3, 1, 1, 1, -1, 1, 1, 1],
![-3, -1, -1, -1, 1, -1, -1, -1],
![-3, -1, -1, -1, 1, -1, -1, -1],
![3, 1, 1, 1, -1, 1, 1, 1],
![-3, -1, -1, -1, 1, -1, -1, -1],
![3, 1, 1, 1, -1, 1, 1, 1],
![3, 1, 1, 1, -1, 1, 1, 1],
![-3, -1, -1, -1, 1, -1, -1, -1],
![3, 1, 1, 1, -1, 1, 1, 1],
![-3, -1, -1, -1, 1, -1, -1, -1],
![-3, -1, -1, -1, 1, -1, -1, -1],
![3, 1, 1, 1, -1, 1, 1, 1],
![-3, -1, -1, -1, 1, -1, -1, -1],
![3, 1, 1, 1, -1, 1, 1, 1],
![3, 1, 1, 1, -1, 1, 1, 1],
![-3, -1, -1, -1, 1, -1, -1, -1],
![3, 1, 1, 1, -1, 1, 1, 1]]

/-- Original source labels of the forward tensor spin factor. -/
def monsterNortonCodeFiveForwardSpinLabel : Fin 64 → Fin 4096 :=
  ![4, 5, 6, 7, 8, 9, 10, 11,
  340, 341, 342, 343, 344, 345, 346, 347,
  676, 677, 678, 679, 680, 681, 682, 683,
  1012, 1013, 1014, 1015, 1016, 1017, 1018, 1019,
  2052, 2053, 2054, 2055, 2056, 2057, 2058, 2059,
  2388, 2389, 2390, 2391, 2392, 2393, 2394, 2395,
  2724, 2725, 2726, 2727, 2728, 2729, 2730, 2731,
  3060, 3061, 3062, 3063, 3064, 3065, 3066, 3067]

/-- Complete integer coefficients of the forward spin factor. -/
def monsterNortonCodeFiveForwardSpinCoefficient : Fin 64 → ℤ :=
  ![1, -1, 1, -1, -1, 1, -1, 1,
  -1, 1, -1, 1, 1, -1, 1, -1,
  -1, 1, -1, 1, 1, -1, 1, -1,
  -1, 1, -1, 1, 1, -1, 1, -1,
  1, -1, 1, -1, -1, 1, -1, 1,
  -1, 1, -1, 1, 1, -1, 1, -1,
  -1, 1, -1, 1, 1, -1, 1, -1,
  -1, 1, -1, 1, 1, -1, 1, -1]

/-- The complete forward tensor Leech factor. -/
def monsterNortonCodeFiveForwardLeech : Fin 24 → ℤ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
  -3, -1, -1, -1, -1, 1, 1, 1]

/-- Certified displayed octad choices in the inverse candidate. -/
def monsterNortonCodeFiveInverseOctadChoice : Fin 8 → Fin 76 :=
  ![34, 35, 52, 53, 54, 55, 58, 59]

/-- Distinct original even sign patterns for each inverse octad. -/
def monsterNortonCodeFiveInverseSign : Fin 8 → Fin 32 → Fin 64 :=
  ![![1, 3, 4, 6, 9, 11, 12, 14,
  17, 19, 20, 22, 25, 27, 28, 30,
  32, 34, 37, 39, 40, 42, 45, 47,
  48, 50, 53, 55, 56, 58, 61, 63],
![2, 3, 6, 7, 8, 9, 12, 13,
  16, 17, 20, 21, 26, 27, 30, 31,
  34, 35, 38, 39, 40, 41, 44, 45,
  48, 49, 52, 53, 58, 59, 62, 63],
![2, 3, 4, 5, 8, 9, 14, 15,
  16, 17, 22, 23, 26, 27, 28, 29,
  34, 35, 36, 37, 40, 41, 46, 47,
  48, 49, 54, 55, 58, 59, 60, 61],
![2, 3, 4, 5, 8, 9, 14, 15,
  16, 17, 22, 23, 26, 27, 28, 29,
  34, 35, 36, 37, 40, 41, 46, 47,
  48, 49, 54, 55, 58, 59, 60, 61],
![2, 3, 4, 5, 8, 9, 14, 15,
  16, 17, 22, 23, 26, 27, 28, 29,
  34, 35, 36, 37, 40, 41, 46, 47,
  48, 49, 54, 55, 58, 59, 60, 61],
![2, 3, 4, 5, 8, 9, 14, 15,
  16, 17, 22, 23, 26, 27, 28, 29,
  34, 35, 36, 37, 40, 41, 46, 47,
  48, 49, 54, 55, 58, 59, 60, 61],
![2, 3, 6, 7, 8, 9, 12, 13,
  18, 19, 22, 23, 24, 25, 28, 29,
  32, 33, 36, 37, 42, 43, 46, 47,
  48, 49, 52, 53, 58, 59, 62, 63],
![2, 3, 6, 7, 8, 9, 12, 13,
  18, 19, 22, 23, 24, 25, 28, 29,
  32, 33, 36, 37, 42, 43, 46, 47,
  48, 49, 52, 53, 58, 59, 62, 63]]

/-- Complete inverse short integer coefficients. -/
def monsterNortonCodeFiveInverseShortCoefficient : Fin 8 → Fin 32 → ℤ :=
  ![![1, -3, -1, 3, 1, -1, -1, 1,
  1, -1, -1, 1, 3, -1, -3, 1,
  1, -3, 1, -3, 1, -1, 1, -1,
  1, -1, 1, -1, 3, -1, 3, -1],
![1, -1, 1, 1, 1, -1, 1, 1,
  1, -1, 1, 1, -1, 1, -1, -1,
  -1, -1, 1, -1, -1, -1, 1, -1,
  -1, -1, 1, -1, 1, 1, -1, 1],
![1, 1, -1, -1, 1, 1, 1, 1,
  -1, -1, -1, -1, 1, 1, -1, -1,
  1, -1, -1, 1, 1, -1, 1, -1,
  -1, 1, -1, 1, 1, -1, -1, 1],
![-1, -1, 1, 1, 1, 1, 1, 1,
  -1, -1, -1, -1, -1, -1, 1, 1,
  -1, 1, 1, -1, 1, -1, 1, -1,
  -1, 1, -1, 1, -1, 1, 1, -1],
![-1, 3, 1, -3, -1, 3, -1, 3,
  1, -3, 1, -3, -1, 3, 1, -3,
  -1, 1, 1, -1, -1, 1, -1, 1,
  1, -1, 1, -1, -1, 1, 1, -1],
![1, -3, -1, 3, -1, 3, -1, 3,
  1, -3, 1, -3, 1, -3, -1, 3,
  1, -1, -1, 1, -1, 1, -1, 1,
  1, -1, 1, -1, 1, -1, -1, 1],
![-1, 1, -1, -1, -1, 1, -1, -1,
  1, 1, -1, 1, 1, 1, -1, 1,
  -1, 1, -1, -1, 1, -1, 1, 1,
  1, 1, -1, 1, -1, -1, 1, -1],
![-3, 3, -3, -3, 1, -1, 1, 1,
  3, 3, -3, 3, -1, -1, 1, -1,
  1, -1, 1, 1, -1, 1, -1, -1,
  -1, -1, 1, -1, 1, 1, -1, 1]]

/-- Original source labels of the inverse tensor spin factor. -/
def monsterNortonCodeFiveInverseSpinLabel : Fin 16 → Fin 4096 :=
  ![692, 698, 948, 954, 1717, 1723, 1973, 1979,
  2740, 2746, 2996, 3002, 3765, 3771, 4021, 4027]

/-- Complete integer coefficients of the inverse spin factor. -/
def monsterNortonCodeFiveInverseSpinCoefficient : Fin 16 → ℤ :=
  ![2, -2, -2, 2, 2, 2, -2, -2,
  -2, 2, 2, -2, -2, -2, 2, 2]

/-- The four original physical columns supporting the inverse tensor factor. -/
def monsterNortonCodeFiveInverseColumns : Fin 4 → Fin 24 := ![3, 15, 18, 21]

/-- The complete inverse tensor Leech factor. -/
def monsterNortonCodeFiveInverseLeech : Fin 24 → ℤ :=
  ![0, 0, 0, 2, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, -2,
  0, 0, -2, 0, 0, -2, 0, 0]

/-- The complete integer coefficient square sum is exactly 512. -/
theorem monsterNortonCodeFive_forward_short_sq :
    (∑ i : Fin 32, ∑ j : Fin 8, monsterNortonCodeFiveForwardShortCoefficient i j ^ 2) = 512 := by
  decide +kernel

/-- The complete integer coefficient square sum is exactly 512. -/
theorem monsterNortonCodeFive_inverse_short_sq :
    (∑ i : Fin 8, ∑ j : Fin 32, monsterNortonCodeFiveInverseShortCoefficient i j ^ 2) = 512 := by
  decide +kernel

/-- The complete integer coefficient square sum is exactly 64. -/
theorem monsterNortonCodeFive_forward_spin_sq :
    (∑ i : Fin 64, monsterNortonCodeFiveForwardSpinCoefficient i ^ 2) = 64 := by
  decide +kernel

/-- The complete integer coefficient square sum is exactly 64. -/
theorem monsterNortonCodeFive_inverse_spin_sq :
    (∑ i : Fin 16, monsterNortonCodeFiveInverseSpinCoefficient i ^ 2) = 64 := by
  decide +kernel

/-- The complete integer coefficient square sum is exactly 16. -/
theorem monsterNortonCodeFive_forward_leech_sq :
    (∑ i : Fin 24, monsterNortonCodeFiveForwardLeech i ^ 2) = 16 := by
  decide +kernel

/-- The complete integer coefficient square sum is exactly 16. -/
theorem monsterNortonCodeFive_inverse_leech_sq :
    (∑ i : Fin 24, monsterNortonCodeFiveInverseLeech i ^ 2) = 16 := by
  decide +kernel

/-- The actual source U numerator transports the entire candidate Leech column. -/
theorem monsterNortonCodeFive_leech_certificate (j : Fin 24) :
    (∑ i : Fin 24, monsterNortonUNumerator1 j i * monsterNortonCodeFiveForwardLeech i) =
      4 * monsterNortonCodeFiveInverseLeech j := by
  revert j
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
