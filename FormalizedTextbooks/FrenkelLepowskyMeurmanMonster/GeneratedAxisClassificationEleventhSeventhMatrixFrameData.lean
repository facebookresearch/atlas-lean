/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationEleventhSectionXi
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSeventhSpatialCount

/-! A genuine original Golay-sign, Mathieu-word and Xi frame matches every actual matrix entry. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

/-- The literal original signed Mathieu letters, in the actual right-to-left product convention. -/
def generatedEleventhSeventhFrameWord : List (Fin 2 × Bool) :=
  [(0, true), (1, false), (0, false), (1, false), (0, true), (1, false), (0, true), (0, true), (1,
      false), (0, true), (0, true)]

/-- The frame permutation is a genuine product of the original Golay automorphisms. -/
def generatedEleventhSeventhFramePermutation : golayAutomorphismSubgroup :=
  (generatedEleventhSeventhFrameWord.map generatedFourthMonomialPermutationLetter).prod

/-- Exact physical forward coordinates of the genuine original permutation. -/
def generatedEleventhSeventhFrameForward : Fin 24 → Fin 24 :=
  ![22, 12, 7, 23, 10, 15, 8, 6, 17, 2, 21, 9, 5, 14, 16, 19, 4, 13, 1, 3, 0, 18, 20, 11]

/-- Exact physical inverse coordinates of the genuine original permutation. -/
def generatedEleventhSeventhFrameBackward : Fin 24 → Fin 24 :=
  ![20, 18, 9, 19, 16, 12, 7, 2, 6, 11, 4, 23, 1, 17, 13, 5, 14, 8, 21, 15, 22, 10, 0, 3]

set_option maxHeartbeats 16000000 in
-- Check both entire original permutation directions, including all inverse letters.
/-- Every physical permutation coordinate agrees with the complete genuine original word. -/
theorem generatedEleventh_seventh_frame_permutation : ∀ i : Fin 24,
    generatedEleventhSeventhFramePermutation.val i = generatedEleventhSeventhFrameForward i ∧
      generatedEleventhSeventhFramePermutation.val.symm i =
        generatedEleventhSeventhFrameBackward i := by
  decide +kernel

/-- Twice the exact physical matrix of the complete genuine original frame. -/
def generatedEleventhSeventhFrameNumerator : Matrix (Fin 24) (Fin 24) ℤ := ![
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 1, 1],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, 1, -1, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, -1, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 1, 1, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, -1, -1, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![-1, -1, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, -1, -1, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, -1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, -1],
  ![-1, 1, -1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 1, 1, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, -1, 1, -1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 1, 1],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, 1, -1],
  ![0, 0, 0, 0, 0, 0, 0, 0, -1, -1, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![-1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![-1, -1, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
]

set_option maxHeartbeats 16000000 in
-- Compare every physical entry with the genuine source code sign and original Xi matrix.
/-- Every integer frame entry retains the actual original code sign and Xi coordinate. -/
theorem generatedEleventh_seventh_frame_numerator : ∀ i j : Fin 24,
    generatedEleventhSeventhFrameNumerator i j =
      (if (sourceGeneratedSignCode (32 : Fin 4096)).val
          (generatedEleventhSeventhFrameBackward i) = 0 then 1 else -1) *
        co1XiNumerator (generatedEleventhSeventhFrameBackward i) j := by
  decide +kernel

set_option maxHeartbeats 64000000 in
-- Check every entry of the entire original integer matrix conjugation.
/-- The genuine complete frame carries precisely the entire actual matrix to the Seventh matrix. -/
theorem generatedEleventh_seventh_frame_integer :
    generatedEleventhSeventhFrameNumerator * generatedEleventhMatrixNumerator *
        generatedEleventhSeventhFrameNumerator.transpose =
      (4 : ℕ) • generatedSeventhMatrixNumerator := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
