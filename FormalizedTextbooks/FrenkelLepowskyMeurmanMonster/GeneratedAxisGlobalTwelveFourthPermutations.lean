/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMonomialWords
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFourthFlagMonomialPermutation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechBinaryMatrix

/-! Integral and binary lattice actions of five literal Golay permutations used by the
Fourth-family forest: the four monomial flag words of the Fourth stabilizer and the flag
correction permutation. Every table is kernel checked against the genuine permutations. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- The four literal monomial flag words, followed by the literal flag correction. -/
def generatedAxisGlobalTwelveFourthPermutation (k : Fin 5) : golayAutomorphismSubgroup :=
  if h : k.val < 4 then generatedFourthMonomialPermutation ⟨k.val, h⟩
  else generatedFourthFlagCorrectionGolay

/-- Candidate complete forward coordinate tables of the five permutations. -/
def generatedAxisGlobalTwelveFourthPermutationForward : Fin 5 → Fin 24 → Fin 24 :=
  ![![21, 14, 17, 3, 6, 5, 4, 10, 8, 9, 7, 11, 12, 22, 1, 16, 15, 2, 18, 23, 20, 0, 13, 19],
    ![3, 1, 2, 0, 4, 6, 5, 7, 11, 9, 10, 8, 12, 14, 13, 15, 22, 20, 23, 21, 17, 19, 16, 18],
    ![0, 12, 22, 19, 4, 9, 7, 6, 8, 5, 10, 11, 1, 13, 20, 16, 15, 17, 23, 3, 14, 21, 2, 18],
    ![1, 0, 3, 2, 4, 5, 6, 7, 11, 10, 9, 8, 14, 15, 12, 13, 16, 17, 18, 19, 21, 20, 23, 22],
    ![0, 1, 2, 3, 4, 5, 6, 7, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22]]

set_option maxHeartbeats 4000000 in
-- Check every coordinate of the five literal permutations.
/-- The forward tables are exactly the actual Golay permutations. -/
theorem generatedAxisGlobalTwelveFourthPermutation_forward : ∀ k : Fin 5, ∀ i : Fin 24,
    (generatedAxisGlobalTwelveFourthPermutation k).val i =
      generatedAxisGlobalTwelveFourthPermutationForward k i := by
  decide +kernel

/-- Physical coordinate matrices of the five permutations. -/
def generatedAxisGlobalTwelveFourthPermutationPhysical (k : Fin 5) :
    Matrix (Fin 24) (Fin 24) ℤ :=
  fun i j => if generatedAxisGlobalTwelveFourthPermutationForward k j = i then 1 else 0

/-- Candidate integral basis actions of the five permutations. -/
def generatedAxisGlobalTwelveFourthPermutationIntegral :
    Fin 5 → Matrix (Fin 24) (Fin 24) ℤ :=
  ![![![5, 5, 6, 2, 2, 2, 2, 3, 2, 2, 5, 6, 2, 3, 3, 1, 5, 1, 4, -11, 5, 5, 4, 2],
      ![-2, -1, -2, -1, -1, -1, -1, -1, -1, -1, -2, -2, -1, -1, -1, -1, -1, 0, -1, 2, -1, -1, -1,
        -1],
      ![-2, -2, -1, -1, -1, -1, -1, -1, -1, -1, -2, -2, -1, -1, -1, -1, -1, 0, -1, 2, -1, -1, -1,
        -1],
      ![0, 0, -1, 1, 0, 0, 0, 0, 0, 0, -1, -1, 0, 0, -1, 0, -1, 0, -1, 2, -1, -1, -1, 0],
      ![0, -1, 0, 0, 0, 0, 1, 0, 0, 0, -1, -1, 0, -1, 0, 0, 0, 0, -1, 3, -1, 0, -1, 0],
      ![0, 0, -1, 0, 0, 1, 0, 0, 0, 0, -1, -1, 0, 0, -1, 0, -1, 0, -1, 1, -1, -1, -1, 0],
      ![-2, -2, -2, -1, 0, -1, -1, -1, -1, -1, -2, -2, -1, -1, -1, -1, -2, -1, -1, 2, -1, -2, -1,
        -1],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 1, 0],
      ![0, -1, -1, 0, 0, 0, 0, -1, 1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 2, -1, -1, -1, 0],
      ![-2, -1, -2, -1, -1, -1, -1, -1, -1, 0, -1, -1, -1, 0, -1, 0, -2, 0, -1, 2, -1, -1, -1, -1],
      ![0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, -1, 0, 0, -1, -1, -1, 2, -1, -1, -1, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0],
      ![-2, -2, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, 0, -1, 0, 0, -2, -1, -1, 2, -1, -1, -1, -1],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1, 0],
      ![0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, -1, 1, 1, 1, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 1, 0, 1, 1, 1, 0],
      ![-2, -1, -2, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, 0, -1, 0, -1, 2, -1, -1, 0, -1],
      ![0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0],
      ![4, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 1, 2, 1, 1, 1, 2, 0, 1, -1, 0, 1, 0, 2],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1]],
    ![![-1, -1, -1, 0, -1, -1, -1, 0, 2, -1, -1, 0, -1, 1, 1, 0, 3, 4, -12, 2, 4, 2, 0, -1],
      ![0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1, 0, -1, -1, 2, -1, -1, 0, 0, 0],
      ![0, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, -1, 2, 0, 0, 0, 0, 0],
      ![2, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 1, -1, 3, 0, -1, 0, 0, 1],
      ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, 3, 0, 0, -1, 0, 0],
      ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 2, 0, -1, 0, 0, 0],
      ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 3, -1, -1, -1, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, -1, 0, 0, -1, 2, 0, -1, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, -1, 0, 0, 0, 2, 0, -1, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1, 0, 0, -1, -1, 2, 0, -1, -1, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, -1, 2, -1, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, 2, -1, -1, -1, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 1, 1, 1, 1, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1]],
    ![![1, 0, 4, 4, 0, 0, 3, 4, 0, 0, 0, 4, 0, 0, 4, 2, 3, 5, -12, 5, 5, 5, 1, 0],
      ![0, 0, -1, 0, 0, 0, -1, -1, 0, 0, 0, -1, 1, 0, -1, 0, 0, -1, 3, -1, 0, -1, 0, 0],
      ![0, 0, 0, -1, 0, 0, -1, -1, 0, 0, 0, -1, 0, 0, -1, -1, 0, -1, 2, -1, -1, -1, 0, 0],
      ![0, 0, 0, -1, 0, 0, -1, -1, 0, 0, 0, -1, 0, 0, -1, -1, -1, -2, 2, -1, -1, -1, -1, 0],
      ![0, 0, -1, -1, 1, 0, -1, -1, 0, 0, 0, -1, 0, 0, -1, -1, 0, -1, 3, -1, -1, -1, 0, 0],
      ![0, 0, -1, 0, 0, 0, -1, -1, 0, 1, 0, 0, 0, 0, -1, 0, -1, -1, 2, -1, -1, -1, -1, 0],
      ![0, 0, -1, -1, 0, 0, -1, -1, 0, 0, 0, -1, 0, 0, -1, -1, -1, -2, 2, -2, -2, -2, -1, 0],
      ![0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 1, 0, 1, 1, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0],
      ![0, 0, 0, -1, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, -1, 2, -1, -1, -1, 0, 0],
      ![0, 0, -1, -1, 0, 0, 0, -1, 0, 0, 1, -1, 0, 0, 0, 0, -1, -1, 2, -1, -2, -1, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0],
      ![0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, -1, 0, 2, -1, -1, -1, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 1, 1, 1, 1, 0],
      ![0, 0, -1, -1, 0, 0, 0, -1, 0, 0, 0, -1, 0, 0, -1, 0, 0, -1, 2, -1, -1, -1, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0],
      ![0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 1, 1, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0],
      ![0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, -1, 1, 1, 1, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1]],
    ![![-1, 0, -1, -1, -1, -1, -1, 0, 2, -1, -1, 0, 2, 3, 1, 1, -1, 2, 1, 0, 3, 2, -14, -1],
      ![2, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 1, -1, 0, 0, -1, 0, 3, 1],
      ![0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, -1, -1, -1, 0, 0, 0, 0, 0, -1, -1, 2, 0],
      ![0, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, -1, -1, 0, 0, 0, 3, 0],
      ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, -1, 0, 0, 0, 0, 0, -1, 3, 0],
      ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0],
      ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, -1, 0, 0, 0, 0, 0, 0, -1, 0, 3, 0],
      ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, -1, -1, -1, -1, 0, -1, -1, 0, -1, -1, 2, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1, 0, 0, 0, -1, 0, 0, -1, 0, 3, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, -1, -1, -1, 0, 0, 0, -1, 0, -1, 0, 2, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, -1, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 0, 0, 0, 0, -1, -1, 2, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -1, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 3, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1]],
    ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 3, 0, 3, 3, 4, 0, 4, 3, 3, 4, -11, 0],
      ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, -1, 0, -1, -1, -1, 0, -1, -1, -1, -1, 2, 0],
      ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, -1, 0, 0, 0, 2, 0],
      ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, -1, 0, -1, 0, -1, -1, 0, -1, 2, 0],
      ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, -1, 0, 0, 0, 0, 0, -1, 3, 0],
      ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -1, 0, -1, 0, -1, 0, 0, -1, -1, -1, 2, 0],
      ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, -1, 0, -1, 0, 3, 0],
      ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, -1, 0, -1, -1, -1, 0, -1, -1, -1, -1, 1, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, -1, 0, -1, -1, -1, 0, -1, -1, -1, -1, 1, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, -1, -1, 0, 0, -1, -1, 0, 0, 2, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, -1, -1, 0, 0, 0, 0, -1, -1, 2, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -1, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -1, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, -1, -1, -1, -1, 2, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 1, 1, 1, 1, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1]]]

set_option maxHeartbeats 20000000 in
-- Verify all five integer lattice basis transport equations entry by entry.
/-- All cached integer entries satisfy the actual basis transport equations. -/
theorem generatedAxisGlobalTwelveFourthPermutation_integral : ∀ k : Fin 5,
    generatedAxisGlobalTwelveFourthPermutationPhysical k * leechBasisMatrix =
      leechBasisMatrix * generatedAxisGlobalTwelveFourthPermutationIntegral k := by
  decide +kernel

/-- The physical matrices act by the genuine coordinate permutations. -/
theorem generatedAxisGlobalTwelveFourthPermutation_embedding (k : Fin 5) (u : Fin 24 → ℤ) :
    (golayPermutationIsometry (generatedAxisGlobalTwelveFourthPermutation k)).val
      (leechCoordinateEmbedding u) =
      leechCoordinateEmbedding (generatedAxisGlobalTwelveFourthPermutationPhysical k *ᵥ u) := by
  have hp : ∀ i j : Fin 24,
      generatedAxisGlobalTwelveFourthPermutationPhysical k i j =
        if (generatedAxisGlobalTwelveFourthPermutation k).val.symm i = j then 1 else 0 := by
    intro i j
    unfold generatedAxisGlobalTwelveFourthPermutationPhysical
    rw [← generatedAxisGlobalTwelveFourthPermutation_forward]
    have he : (generatedAxisGlobalTwelveFourthPermutation k).val j = i ↔
        (generatedAxisGlobalTwelveFourthPermutation k).val.symm i = j := by
      exact (Equiv.eq_symm_apply _).symm.trans eq_comm
    simp only [he]
  ext i
  simp [golayPermutationIsometry, golayRealPermute_apply, leechCoordinateEmbedding,
    Matrix.mulVec, dotProduct, hp]

/-- The cached integral basis action is the full actual lattice action. -/
theorem generatedAxisGlobalTwelveFourthPermutation_basis (k : Fin 5) (u : Fin 24 → ℤ) :
    (golayPermutationIsometry (generatedAxisGlobalTwelveFourthPermutation k)).val
      (leechCoordinateEmbedding (leechBasisMatrix *ᵥ u)) =
      leechCoordinateEmbedding (leechBasisMatrix *ᵥ
        (generatedAxisGlobalTwelveFourthPermutationIntegral k *ᵥ u)) := by
  rw [generatedAxisGlobalTwelveFourthPermutation_embedding, Matrix.mulVec_mulVec,
    generatedAxisGlobalTwelveFourthPermutation_integral, ← Matrix.mulVec_mulVec]

/-- Binary matrices in the actual hyperbolic coordinates. -/
def generatedAxisGlobalTwelveFourthPermutationBinary (k : Fin 5) :
    Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  leechHyperbolicInverse *
    (generatedAxisGlobalTwelveFourthPermutationIntegral k).map (Int.castRingHom (ZMod 2)) *
      leechHyperbolicMatrix

/-- The binary matrices are the genuine Conway quotient actions of the five permutations. -/
theorem generatedAxisGlobalTwelveFourthPermutation_binary (k : Fin 5) (v : Fin 24 → ZMod 2) :
    co1BinaryAction (QuotientGroup.mk' signsSubgroup
      (golayPermutationIsometry (generatedAxisGlobalTwelveFourthPermutation k))) v =
        generatedAxisGlobalTwelveFourthPermutationBinary k *ᵥ v :=
  leechBinaryAction_of_basis_certificate _ _
    (generatedAxisGlobalTwelveFourthPermutation_basis k) v

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
