/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthPermutationGenerationProfileFast

/-! Eight finite incidence certificates for the genuine code14 and pair stabilizer. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Prefix lengths for the eight actual octad profiles. -/
def generatedFourthPermutationProfileLevels : Fin 8 → ℕ := ![0, 1, 2, 3, 4, 5, 6, 6]

/-- Prefix bit patterns for the eight actual octad profiles. -/
def generatedFourthPermutationProfilePatterns : Fin 8 → ℕ := ![0, 0, 0, 0, 0, 0, 32, 10]

/-- Pair intersection sizes for the eight actual octad profiles. -/
def generatedFourthPermutationProfilePairs : Fin 8 → ℕ := ![2, 2, 2, 0, 2, 2, 2, 0]

/-- Explicit complete octad lists for the eight selected actual profiles. -/
def generatedFourthPermutationProfileLists : Fin 8 → Finset (Fin 4096) :=
  ![([3, 5, 9, 115, 117, 120, 126, 179, 180, 185, 190, 242, 245, 249, 254, 437, 446, 633, 638,
      1011, 1022, 1308, 1318, 1373, 1377, 1425, 1441, 1489, 1511, 1562, 1580, 1617, 1633, 1681,
      1709, 1755, 1761, 1814, 1834, 1873, 1899, 1943, 1953, 2001, 2017, 2049, 2481, 2490, 2673,
      2678, 3057, 3068, 3102, 3118, 3155, 3173, 3225, 3235, 3285, 3305] : List (Fin
      4096)).toFinset, ([3, 5, 9, 115, 117, 120, 126, 179, 180, 185, 190, 242, 245, 249, 254, 437,
      446, 633, 638, 1011, 1022, 1308, 1318, 1373, 1377, 1425, 1441, 1489, 1511, 1562, 1580, 1617,
      1633, 1681, 1709, 1755, 1761, 1814, 1834, 1873, 1899, 1943, 1953, 2001, 2017] : List (Fin
      4096)).toFinset, ([3, 5, 9, 115, 117, 120, 126, 179, 180, 185, 190, 242, 245, 249, 254, 437,
      446, 1562, 1580, 1617, 1633, 1681, 1709, 1755, 1761, 1814, 1834, 1873, 1899, 1943, 1953,
      2001, 2017] : List (Fin 4096)).toFinset, ([7, 11, 13, 112, 118, 123, 125, 176, 183, 186,
      189, 240, 247, 251, 252, 1816, 1828, 1887, 1893, 1945, 1967, 2015, 2031] : List (Fin
      4096)).toFinset, ([3, 5, 9, 115, 117, 120, 126, 179, 180, 185, 190, 242, 245, 249, 254] :
      List (Fin 4096)).toFinset, ([3, 5, 9, 115, 117, 179, 185, 245, 249] : List (Fin
      4096)).toFinset, ([3, 5, 9, 115, 117, 179, 185, 245, 249] : List (Fin 4096)).toFinset,
      ([624] : List (Fin 4096)).toFinset]

/-- Actual incidence counts, indexed by physical coordinate and selected profile. -/
def generatedFourthPermutationProfileCounts : Fin 24 → Fin 8 → ℕ :=
  ![![15, 0, 0, 0, 0, 0, 0, 0],
    ![15, 12, 0, 0, 0, 0, 0, 1],
    ![15, 12, 10, 0, 0, 0, 0, 0],
    ![15, 12, 10, 8, 0, 0, 0, 1],
    ![20, 15, 11, 15, 6, 0, 0, 0],
    ![20, 15, 11, 15, 6, 4, 4, 0],
    ![20, 15, 11, 15, 6, 4, 4, 1],
    ![20, 15, 11, 15, 6, 4, 4, 1],
    ![60, 45, 33, 0, 15, 9, 9, 0],
    ![20, 15, 11, 16, 3, 3, 3, 1],
    ![20, 15, 11, 16, 3, 3, 3, 1],
    ![60, 45, 33, 0, 15, 9, 9, 0],
    ![15, 12, 9, 7, 5, 3, 3, 0],
    ![15, 12, 9, 7, 5, 3, 3, 0],
    ![15, 12, 9, 7, 5, 3, 3, 0],
    ![15, 12, 9, 7, 5, 3, 3, 0],
    ![15, 12, 10, 7, 5, 3, 3, 0],
    ![15, 12, 10, 7, 5, 3, 3, 0],
    ![15, 12, 10, 7, 5, 3, 3, 0],
    ![15, 12, 10, 7, 5, 3, 3, 0],
    ![15, 12, 9, 7, 5, 3, 3, 0],
    ![15, 12, 9, 7, 5, 3, 3, 1],
    ![15, 12, 9, 7, 5, 3, 3, 1],
    ![15, 12, 9, 7, 5, 3, 3, 0]]

/-- Candidate coordinate orbits of the seven successive actual prefix stabilizers. -/
def generatedFourthPermutationEligible : Fin 7 → Finset (Fin 24) :=
  ![([0, 1, 2, 3, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23] : List (Fin 24)).toFinset, ([1,
      2, 3, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23] : List (Fin 24)).toFinset, ([2, 3, 16,
      17, 18, 19] : List (Fin 24)).toFinset, ([3] : List (Fin 24)).toFinset, ([4, 5, 6, 7] : List
      (Fin 24)).toFinset, ([8, 11] : List (Fin 24)).toFinset, ([5] : List (Fin 24)).toFinset]

/-- Sizes of the candidate coordinate orbits. -/
def generatedFourthPermutationOrbitSizes : Fin 7 → ℕ := ![16, 15, 6, 1, 4, 2, 1]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 80000000 in
-- The finite filter checks all genuine octads, using the proved integer profile formulas.
theorem generatedFourth_permutation_profile_lists : ∀ r : Fin 8,
    generatedFourthPermutationProfileOctads (generatedFourthPermutationProfileLevels r)
      (generatedFourthPermutationProfilePatterns r) 4 (generatedFourthPermutationProfilePairs r) =
        generatedFourthPermutationProfileLists r := by
  intro r
  unfold generatedFourthPermutationProfileOctads
  simp only [generatedFourth_permutation_pattern_fast,
    generatedFourth_permutation_overlap_fast, generatedFourth_permutation_pair_fast]
  have h : ∀ r : Fin 8,
      golayOctads.filter (fun d =>
        generatedFourthPermutationFastPattern (generatedFourthPermutationProfileLevels r) d =
          generatedFourthPermutationProfilePatterns r ∧
        generatedFourthPermutationFastOverlap d = 4 ∧
        generatedFourthPermutationFastPair d = generatedFourthPermutationProfilePairs r) =
          generatedFourthPermutationProfileLists r := by decide +kernel
  exact h r

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
-- Count each certified finite list at all 24 genuine physical coordinates.
theorem generatedFourth_permutation_profile_counts : ∀ r : Fin 8, ∀ i : Fin 24,
    generatedFourthPermutationIncidence (generatedFourthPermutationProfileLevels r)
      (generatedFourthPermutationProfilePatterns r) 4 (generatedFourthPermutationProfilePairs r) i =
        generatedFourthPermutationProfileCounts i r := by
  intro r i
  unfold generatedFourthPermutationIncidence
  rw [generatedFourth_permutation_profile_lists]
  have h : ∀ r : Fin 8, ∀ i : Fin 24,
      ((generatedFourthPermutationProfileLists r).filter
        (fun d => golayEncoder (golayLabelCoefficients d) i = 1)).card =
          generatedFourthPermutationProfileCounts i r := by decide +kernel
  exact h r i

/-- The certified incidence invariants bound each successive actual coordinate orbit. -/
theorem generatedFourth_permutation_profile_separates : ∀ k : Fin 7, ∀ i : Fin 24,
    (∀ r : Fin 8, generatedFourthPermutationProfileLevels r = k.val →
      generatedFourthPermutationProfileCounts i r =
        generatedFourthPermutationProfileCounts (golayBasePoints k) r) →
      i ∈ generatedFourthPermutationEligible k := by
  decide +kernel

/-- Candidate orbit cardinalities are checked directly from the explicit coordinate lists. -/
theorem generatedFourth_permutation_eligible_card : ∀ k : Fin 7,
    (generatedFourthPermutationEligible k).card = generatedFourthPermutationOrbitSizes k := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
