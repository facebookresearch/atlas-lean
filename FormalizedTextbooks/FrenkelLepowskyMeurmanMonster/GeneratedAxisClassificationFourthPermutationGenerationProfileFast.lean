/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthPermutationGenerationIncidence

/-! Integer bit formulas for the genuine octad-incidence profiles. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

/-- Bit formula for the prefix pattern of an actual Golay label. -/
def generatedFourthPermutationFastPattern (k : ℕ) (d : Fin 4096) : ℕ :=
  ∑ j : Fin 7, if j.val < k then
    (if (golayEncodedMask d.val).testBit (golayBasePoints j).val then 1 else 0) *
      2 ^ j.val else 0

/-- Bit formula for intersection with the actual coordinate octad 4 through 11. -/
def generatedFourthPermutationFastOverlap (d : Fin 4096) : ℕ :=
  ∑ i : Fin 24, if 4 ≤ i.val ∧ i.val < 12 then
    (if (golayEncodedMask d.val).testBit i.val then 1 else 0) else 0

/-- Bit formula for intersection with the actual unordered pair 8,11. -/
def generatedFourthPermutationFastPair (d : Fin 4096) : ℕ :=
  (if (golayEncodedMask d.val).testBit 8 then 1 else 0) +
    (if (golayEncodedMask d.val).testBit 11 then 1 else 0)

/-- The published encoder identifies code14 with the physical octad 4 through 11. -/
theorem generatedFourth_permutation_code14_coordinate (i : Fin 24) :
    (golayEncoder (golayLabelCoefficients 14) i).val =
      if 4 ≤ i.val ∧ i.val < 12 then 1 else 0 := by
  rw [golayLabelEncoder_match]
  have h : ∀ i : Fin 24,
      (if (golayEncodedMask 14).testBit i.val then 1 else 0 : ℕ) =
        if 4 ≤ i.val ∧ i.val < 12 then 1 else 0 := by decide +kernel
  exact h i

/-- The actual prefix profile agrees with its integer bit formula. -/
theorem generatedFourth_permutation_pattern_fast (k : ℕ) (d : Fin 4096) :
    generatedFourthPermutationBasePattern k d = generatedFourthPermutationFastPattern k d := by
  simp only [generatedFourthPermutationBasePattern, generatedFourthPermutationFastPattern,
    golayLabelEncoder_match]

/-- The actual code14 intersection agrees with its integer bit formula. -/
theorem generatedFourth_permutation_overlap_fast (d : Fin 4096) :
    generatedFourthPermutationOctadOverlap d = generatedFourthPermutationFastOverlap d := by
  unfold generatedFourthPermutationOctadOverlap generatedFourthPermutationFastOverlap
  apply Finset.sum_congr rfl
  intro i _
  rw [generatedFourth_permutation_code14_coordinate, golayLabelEncoder_match]
  split_ifs <;> simp_all

/-- The actual pair intersection agrees with its integer bit formula. -/
theorem generatedFourth_permutation_pair_fast (d : Fin 4096) :
    generatedFourthPermutationPairOverlap d = generatedFourthPermutationFastPair d := by
  have h (f : Fin 24 → ℕ) :
      (∑ i : Fin 24, if i = 8 ∨ i = 11 then f i else 0) = f 8 + f 11 := by
    simp [Fin.sum_univ_succ]
  rw [generatedFourthPermutationPairOverlap, h]
  simp only [generatedFourthPermutationFastPair, golayLabelEncoder_match]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
