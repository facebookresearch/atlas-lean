/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact finite source-dictionary data for a sparse second-input half-word candidate. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsOctadCoordinates

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- First physical coordinates of the eight A and C terms. -/
def monsterNortonSecondHalfPairFirst : Fin 8 → Fin 24 :=
  ![0, 1, 4, 5, 8, 9, 12, 13]

/-- Second physical coordinates of the eight A and C terms. -/
def monsterNortonSecondHalfPairSecond : Fin 8 → Fin 24 :=
  ![2, 3, 6, 7, 10, 11, 14, 15]

/-- Integer coefficients of the eight A terms, with common denominator sixteen. -/
def monsterNortonSecondHalfPairCoefficient : Fin 8 → ℤ :=
  ![-1, 1, -1, 1, -1, 1, -1, 1]

/-- The fourteen original source Golay codes of the supported octad blocks. -/
def monsterNortonSecondHalfOctadCode : Fin 14 → Fin 4096 :=
  ![3, 13, 14, 672, 675, 685, 686, 2049, 2050, 2063, 2721, 2722, 2732, 2735]

/-- The sixteen original even-sign labels supported in each octad block. -/
def monsterNortonSecondHalfOctadSign : Fin 14 → Fin 16 → Fin 64 :=
  ![
    ![1, 4, 11, 14, 17, 20, 27, 30, 34, 39, 40, 45, 50, 55, 56, 61],
    ![1, 4, 11, 14, 17, 20, 27, 30, 34, 39, 40, 45, 50, 55, 56, 61],
    ![1, 4, 11, 14, 17, 20, 27, 30, 34, 39, 40, 45, 50, 55, 56, 61],
    ![0, 3, 12, 15, 21, 22, 25, 26, 37, 38, 41, 42, 48, 51, 60, 63],
    ![5, 6, 9, 10, 16, 19, 28, 31, 32, 35, 44, 47, 53, 54, 57, 58],
    ![4, 7, 8, 11, 17, 18, 29, 30, 33, 34, 45, 46, 52, 55, 56, 59],
    ![1, 2, 13, 14, 20, 23, 24, 27, 36, 39, 40, 43, 49, 50, 61, 62],
    ![1, 4, 11, 14, 17, 20, 27, 30, 34, 39, 40, 45, 50, 55, 56, 61],
    ![1, 4, 11, 14, 17, 20, 27, 30, 34, 39, 40, 45, 50, 55, 56, 61],
    ![1, 4, 11, 14, 17, 20, 27, 30, 34, 39, 40, 45, 50, 55, 56, 61],
    ![4, 7, 8, 11, 17, 18, 29, 30, 33, 34, 45, 46, 52, 55, 56, 59],
    ![1, 2, 13, 14, 20, 23, 24, 27, 36, 39, 40, 43, 49, 50, 61, 62],
    ![0, 3, 12, 15, 21, 22, 25, 26, 37, 38, 41, 42, 48, 51, 60, 63],
    ![5, 6, 9, 10, 16, 19, 28, 31, 32, 35, 44, 47, 53, 54, 57, 58]
  ]

/-- Integer octad coefficients, with common denominator sixteen. -/
def monsterNortonSecondHalfOctadCoefficient : Fin 14 → Fin 16 → ℤ :=
  ![
    ![-1, 1, 1, -1, 1, -1, -1, 1, -1, -1, -1, -1, -1, -1, -1, -1],
    ![-1, 1, 1, -1, 1, -1, -1, 1, -1, -1, -1, -1, -1, -1, -1, -1],
    ![-1, 1, 1, -1, 1, -1, -1, 1, -1, -1, -1, -1, -1, -1, -1, -1],
    ![-1, 1, 1, -1, -1, -1, -1, -1, -1, -1, -1, -1, 1, -1, -1, 1],
    ![-1, -1, -1, -1, -1, 1, 1, -1, 1, -1, -1, 1, -1, -1, -1, -1],
    ![-1, 1, 1, -1, -1, -1, -1, -1, -1, -1, -1, -1, 1, -1, -1, 1],
    ![-1, -1, -1, -1, -1, 1, 1, -1, 1, -1, -1, 1, -1, -1, -1, -1],
    ![1, -1, -1, 1, -1, 1, 1, -1, 1, 1, 1, 1, 1, 1, 1, 1],
    ![1, -1, -1, 1, -1, 1, 1, -1, 1, 1, 1, 1, 1, 1, 1, 1],
    ![1, -1, -1, 1, -1, 1, 1, -1, 1, 1, 1, 1, 1, 1, 1, 1],
    ![1, 1, 1, 1, 1, -1, -1, 1, -1, 1, 1, -1, 1, 1, 1, 1],
    ![1, -1, -1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 1, 1, -1],
    ![1, 1, 1, 1, 1, -1, -1, 1, -1, 1, 1, -1, 1, 1, 1, 1],
    ![1, -1, -1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 1, 1, -1]
  ]

/-- Every physical pair is displayed in the actual increasing coordinate order. -/
theorem monsterNortonSecondHalfPair_lt (i : Fin 8) :
    monsterNortonSecondHalfPairFirst i < monsterNortonSecondHalfPairSecond i := by
  revert i
  decide +kernel

/-- The eight displayed physical pairs are distinct. -/
theorem monsterNortonSecondHalfPair_eq_iff (i j : Fin 8) :
    monsterNortonSecondHalfPairFirst i = monsterNortonSecondHalfPairFirst j ∧
      monsterNortonSecondHalfPairSecond i = monsterNortonSecondHalfPairSecond j ↔ i = j := by
  revert i j
  decide +kernel

/-- Each displayed octad code is a genuine weight-eight Golay codeword. -/
theorem monsterNortonSecondHalfOctad_weight (d : Fin 14) :
    golayMaskWeight (golayEncodedMask (monsterNortonSecondHalfOctadCode d).val) = 8 := by
  revert d
  decide +kernel

/-- The fourteen source octad codes are pairwise distinct. -/
theorem monsterNortonSecondHalfOctad_eq_iff (d f : Fin 14) :
    monsterNortonSecondHalfOctadCode d = monsterNortonSecondHalfOctadCode f ↔ d = f := by
  revert d f
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the 3584 finite within-block label comparisons.
/-- Every block uses sixteen distinct original even-sign labels. -/
theorem monsterNortonSecondHalfOctadSign_eq_iff (d : Fin 14) (e f : Fin 16) :
    monsterNortonSecondHalfOctadSign d e = monsterNortonSecondHalfOctadSign d f ↔ e = f := by
  revert d e f
  decide +kernel

/-- Every A coefficient has its exact integer square one. -/
theorem monsterNortonSecondHalfPairCoefficient_sq (i : Fin 8) :
    monsterNortonSecondHalfPairCoefficient i ^ 2 = 1 := by
  revert i
  decide +kernel

/-- Every supported octad coefficient has its exact integer square one. -/
theorem monsterNortonSecondHalfOctadCoefficient_sq (d : Fin 14) (e : Fin 16) :
    monsterNortonSecondHalfOctadCoefficient d e ^ 2 = 1 := by
  revert d e
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
