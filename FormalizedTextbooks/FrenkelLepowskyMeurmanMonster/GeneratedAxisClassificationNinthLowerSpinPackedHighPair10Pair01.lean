/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinPackedHighPairGeneric
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinTensorCircuitData

/-! Complete original source words, low-bit gaps and signed-word equations for
required Ninth generator 10, Fourier pair 1. Every original packed slot remains covered. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option maxRecDepth 100000

/-- The original source word at its full eight-bit prefix. -/
def generatedNinthLowerSpinPackedHighPair10Pair01Word (stage : ℕ) (j : Fin 24) (a : Fin 256) : ℕ :=
  generatedNinthLowerSpinTensorStageWords 10 stage j
    ⟨a.val / 16, by omega⟩ ⟨a.val % 16, Nat.mod_lt _ (by decide)⟩

/-- Toggling a genuine Fourier bit in the complete original word prefix. -/
def generatedNinthLowerSpinPackedHighPair10Pair01Xor := generatedNinthLowerSpinPackedPrefixXor

/-- Four original source words in the order of the paired Fourier expansion. -/
def generatedNinthLowerSpinPackedHighPair10Pair01Sources (j : Fin 24) (a : Fin 256) : Fin 4 → ℕ :=
  generatedNinthLowerSpinPackedHighSources (generatedNinthLowerSpinPackedHighPair10Pair01Word 1 j) 2 3 a

/-- The complete original paired Fourier signs. -/
def generatedNinthLowerSpinPackedHighPair10Pair01Coefficients (a : Fin 256) : Fin 4 → ℤ :=
  generatedNinthLowerSpinPackedHighCoefficients 2 3 a

/-- Range and low-bit certificates refer to both complete original source stages. -/
def generatedNinthLowerSpinPackedHighPair10Pair01Condition (j : Fin 24) (a : Fin 256) : Prop :=
  generatedNinthLowerSpinPackedHighPair10Pair01Word 1 j a < 512 ^ 16 ∧
  generatedNinthLowerSpinPackedHighPair10Pair01Word 2 j a < 512 ^ 16 ∧
  generatedNinthLowerSpinPackedHighPair10Pair01Word 1 j a &&& generatedRootEightPackedGapEightMask = 0 ∧
  generatedNinthLowerSpinPackedHighPair10Pair01Word 2 j a &&& generatedRootEightPackedGapEightMask = 0 ∧
  (∑ z : Fin 4, generatedNinthLowerSpinPackedHighPair10Pair01Coefficients a z *
    generatedRootEightPackedSignedWord (generatedNinthLowerSpinPackedHighPair10Pair01Sources j a z)) =
      2 * generatedRootEightPackedSignedWord (generatedNinthLowerSpinPackedHighPair10Pair01Word 2 j a)

set_option maxHeartbeats 8000000 in
-- Check one complete source column using all original signed whole words.
private theorem column_00 : ∀ a : Fin 256, generatedNinthLowerSpinPackedHighPair10Pair01Condition 0 a := by
  dsimp only [generatedNinthLowerSpinPackedHighPair10Pair01Condition, generatedNinthLowerSpinPackedHighPair10Pair01Sources,
    generatedNinthLowerSpinPackedHighSources, generatedNinthLowerSpinPackedHighPair10Pair01Word,
    generatedNinthLowerSpinTensorStageWords, generatedNinthLowerSpinTensorStageWords10]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete source column using all original signed whole words.
private theorem column_01 : ∀ a : Fin 256, generatedNinthLowerSpinPackedHighPair10Pair01Condition 1 a := by
  dsimp only [generatedNinthLowerSpinPackedHighPair10Pair01Condition, generatedNinthLowerSpinPackedHighPair10Pair01Sources,
    generatedNinthLowerSpinPackedHighSources, generatedNinthLowerSpinPackedHighPair10Pair01Word,
    generatedNinthLowerSpinTensorStageWords, generatedNinthLowerSpinTensorStageWords10]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete source column using all original signed whole words.
private theorem column_02 : ∀ a : Fin 256, generatedNinthLowerSpinPackedHighPair10Pair01Condition 2 a := by
  dsimp only [generatedNinthLowerSpinPackedHighPair10Pair01Condition, generatedNinthLowerSpinPackedHighPair10Pair01Sources,
    generatedNinthLowerSpinPackedHighSources, generatedNinthLowerSpinPackedHighPair10Pair01Word,
    generatedNinthLowerSpinTensorStageWords, generatedNinthLowerSpinTensorStageWords10]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete source column using all original signed whole words.
private theorem column_03 : ∀ a : Fin 256, generatedNinthLowerSpinPackedHighPair10Pair01Condition 3 a := by
  dsimp only [generatedNinthLowerSpinPackedHighPair10Pair01Condition, generatedNinthLowerSpinPackedHighPair10Pair01Sources,
    generatedNinthLowerSpinPackedHighSources, generatedNinthLowerSpinPackedHighPair10Pair01Word,
    generatedNinthLowerSpinTensorStageWords, generatedNinthLowerSpinTensorStageWords10]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete source column using all original signed whole words.
private theorem column_04 : ∀ a : Fin 256, generatedNinthLowerSpinPackedHighPair10Pair01Condition 4 a := by
  dsimp only [generatedNinthLowerSpinPackedHighPair10Pair01Condition, generatedNinthLowerSpinPackedHighPair10Pair01Sources,
    generatedNinthLowerSpinPackedHighSources, generatedNinthLowerSpinPackedHighPair10Pair01Word,
    generatedNinthLowerSpinTensorStageWords, generatedNinthLowerSpinTensorStageWords10]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete source column using all original signed whole words.
private theorem column_05 : ∀ a : Fin 256, generatedNinthLowerSpinPackedHighPair10Pair01Condition 5 a := by
  dsimp only [generatedNinthLowerSpinPackedHighPair10Pair01Condition, generatedNinthLowerSpinPackedHighPair10Pair01Sources,
    generatedNinthLowerSpinPackedHighSources, generatedNinthLowerSpinPackedHighPair10Pair01Word,
    generatedNinthLowerSpinTensorStageWords, generatedNinthLowerSpinTensorStageWords10]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete source column using all original signed whole words.
private theorem column_06 : ∀ a : Fin 256, generatedNinthLowerSpinPackedHighPair10Pair01Condition 6 a := by
  dsimp only [generatedNinthLowerSpinPackedHighPair10Pair01Condition, generatedNinthLowerSpinPackedHighPair10Pair01Sources,
    generatedNinthLowerSpinPackedHighSources, generatedNinthLowerSpinPackedHighPair10Pair01Word,
    generatedNinthLowerSpinTensorStageWords, generatedNinthLowerSpinTensorStageWords10]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete source column using all original signed whole words.
private theorem column_07 : ∀ a : Fin 256, generatedNinthLowerSpinPackedHighPair10Pair01Condition 7 a := by
  dsimp only [generatedNinthLowerSpinPackedHighPair10Pair01Condition, generatedNinthLowerSpinPackedHighPair10Pair01Sources,
    generatedNinthLowerSpinPackedHighSources, generatedNinthLowerSpinPackedHighPair10Pair01Word,
    generatedNinthLowerSpinTensorStageWords, generatedNinthLowerSpinTensorStageWords10]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete source column using all original signed whole words.
private theorem column_08 : ∀ a : Fin 256, generatedNinthLowerSpinPackedHighPair10Pair01Condition 8 a := by
  dsimp only [generatedNinthLowerSpinPackedHighPair10Pair01Condition, generatedNinthLowerSpinPackedHighPair10Pair01Sources,
    generatedNinthLowerSpinPackedHighSources, generatedNinthLowerSpinPackedHighPair10Pair01Word,
    generatedNinthLowerSpinTensorStageWords, generatedNinthLowerSpinTensorStageWords10]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete source column using all original signed whole words.
private theorem column_09 : ∀ a : Fin 256, generatedNinthLowerSpinPackedHighPair10Pair01Condition 9 a := by
  dsimp only [generatedNinthLowerSpinPackedHighPair10Pair01Condition, generatedNinthLowerSpinPackedHighPair10Pair01Sources,
    generatedNinthLowerSpinPackedHighSources, generatedNinthLowerSpinPackedHighPair10Pair01Word,
    generatedNinthLowerSpinTensorStageWords, generatedNinthLowerSpinTensorStageWords10]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete source column using all original signed whole words.
private theorem column_10 : ∀ a : Fin 256, generatedNinthLowerSpinPackedHighPair10Pair01Condition 10 a := by
  dsimp only [generatedNinthLowerSpinPackedHighPair10Pair01Condition, generatedNinthLowerSpinPackedHighPair10Pair01Sources,
    generatedNinthLowerSpinPackedHighSources, generatedNinthLowerSpinPackedHighPair10Pair01Word,
    generatedNinthLowerSpinTensorStageWords, generatedNinthLowerSpinTensorStageWords10]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete source column using all original signed whole words.
private theorem column_11 : ∀ a : Fin 256, generatedNinthLowerSpinPackedHighPair10Pair01Condition 11 a := by
  dsimp only [generatedNinthLowerSpinPackedHighPair10Pair01Condition, generatedNinthLowerSpinPackedHighPair10Pair01Sources,
    generatedNinthLowerSpinPackedHighSources, generatedNinthLowerSpinPackedHighPair10Pair01Word,
    generatedNinthLowerSpinTensorStageWords, generatedNinthLowerSpinTensorStageWords10]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete source column using all original signed whole words.
private theorem column_12 : ∀ a : Fin 256, generatedNinthLowerSpinPackedHighPair10Pair01Condition 12 a := by
  dsimp only [generatedNinthLowerSpinPackedHighPair10Pair01Condition, generatedNinthLowerSpinPackedHighPair10Pair01Sources,
    generatedNinthLowerSpinPackedHighSources, generatedNinthLowerSpinPackedHighPair10Pair01Word,
    generatedNinthLowerSpinTensorStageWords, generatedNinthLowerSpinTensorStageWords10]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete source column using all original signed whole words.
private theorem column_13 : ∀ a : Fin 256, generatedNinthLowerSpinPackedHighPair10Pair01Condition 13 a := by
  dsimp only [generatedNinthLowerSpinPackedHighPair10Pair01Condition, generatedNinthLowerSpinPackedHighPair10Pair01Sources,
    generatedNinthLowerSpinPackedHighSources, generatedNinthLowerSpinPackedHighPair10Pair01Word,
    generatedNinthLowerSpinTensorStageWords, generatedNinthLowerSpinTensorStageWords10]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete source column using all original signed whole words.
private theorem column_14 : ∀ a : Fin 256, generatedNinthLowerSpinPackedHighPair10Pair01Condition 14 a := by
  dsimp only [generatedNinthLowerSpinPackedHighPair10Pair01Condition, generatedNinthLowerSpinPackedHighPair10Pair01Sources,
    generatedNinthLowerSpinPackedHighSources, generatedNinthLowerSpinPackedHighPair10Pair01Word,
    generatedNinthLowerSpinTensorStageWords, generatedNinthLowerSpinTensorStageWords10]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete source column using all original signed whole words.
private theorem column_15 : ∀ a : Fin 256, generatedNinthLowerSpinPackedHighPair10Pair01Condition 15 a := by
  dsimp only [generatedNinthLowerSpinPackedHighPair10Pair01Condition, generatedNinthLowerSpinPackedHighPair10Pair01Sources,
    generatedNinthLowerSpinPackedHighSources, generatedNinthLowerSpinPackedHighPair10Pair01Word,
    generatedNinthLowerSpinTensorStageWords, generatedNinthLowerSpinTensorStageWords10]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete source column using all original signed whole words.
private theorem column_16 : ∀ a : Fin 256, generatedNinthLowerSpinPackedHighPair10Pair01Condition 16 a := by
  dsimp only [generatedNinthLowerSpinPackedHighPair10Pair01Condition, generatedNinthLowerSpinPackedHighPair10Pair01Sources,
    generatedNinthLowerSpinPackedHighSources, generatedNinthLowerSpinPackedHighPair10Pair01Word,
    generatedNinthLowerSpinTensorStageWords, generatedNinthLowerSpinTensorStageWords10]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete source column using all original signed whole words.
private theorem column_17 : ∀ a : Fin 256, generatedNinthLowerSpinPackedHighPair10Pair01Condition 17 a := by
  dsimp only [generatedNinthLowerSpinPackedHighPair10Pair01Condition, generatedNinthLowerSpinPackedHighPair10Pair01Sources,
    generatedNinthLowerSpinPackedHighSources, generatedNinthLowerSpinPackedHighPair10Pair01Word,
    generatedNinthLowerSpinTensorStageWords, generatedNinthLowerSpinTensorStageWords10]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete source column using all original signed whole words.
private theorem column_18 : ∀ a : Fin 256, generatedNinthLowerSpinPackedHighPair10Pair01Condition 18 a := by
  dsimp only [generatedNinthLowerSpinPackedHighPair10Pair01Condition, generatedNinthLowerSpinPackedHighPair10Pair01Sources,
    generatedNinthLowerSpinPackedHighSources, generatedNinthLowerSpinPackedHighPair10Pair01Word,
    generatedNinthLowerSpinTensorStageWords, generatedNinthLowerSpinTensorStageWords10]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete source column using all original signed whole words.
private theorem column_19 : ∀ a : Fin 256, generatedNinthLowerSpinPackedHighPair10Pair01Condition 19 a := by
  dsimp only [generatedNinthLowerSpinPackedHighPair10Pair01Condition, generatedNinthLowerSpinPackedHighPair10Pair01Sources,
    generatedNinthLowerSpinPackedHighSources, generatedNinthLowerSpinPackedHighPair10Pair01Word,
    generatedNinthLowerSpinTensorStageWords, generatedNinthLowerSpinTensorStageWords10]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete source column using all original signed whole words.
private theorem column_20 : ∀ a : Fin 256, generatedNinthLowerSpinPackedHighPair10Pair01Condition 20 a := by
  dsimp only [generatedNinthLowerSpinPackedHighPair10Pair01Condition, generatedNinthLowerSpinPackedHighPair10Pair01Sources,
    generatedNinthLowerSpinPackedHighSources, generatedNinthLowerSpinPackedHighPair10Pair01Word,
    generatedNinthLowerSpinTensorStageWords, generatedNinthLowerSpinTensorStageWords10]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete source column using all original signed whole words.
private theorem column_21 : ∀ a : Fin 256, generatedNinthLowerSpinPackedHighPair10Pair01Condition 21 a := by
  dsimp only [generatedNinthLowerSpinPackedHighPair10Pair01Condition, generatedNinthLowerSpinPackedHighPair10Pair01Sources,
    generatedNinthLowerSpinPackedHighSources, generatedNinthLowerSpinPackedHighPair10Pair01Word,
    generatedNinthLowerSpinTensorStageWords, generatedNinthLowerSpinTensorStageWords10]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete source column using all original signed whole words.
private theorem column_22 : ∀ a : Fin 256, generatedNinthLowerSpinPackedHighPair10Pair01Condition 22 a := by
  dsimp only [generatedNinthLowerSpinPackedHighPair10Pair01Condition, generatedNinthLowerSpinPackedHighPair10Pair01Sources,
    generatedNinthLowerSpinPackedHighSources, generatedNinthLowerSpinPackedHighPair10Pair01Word,
    generatedNinthLowerSpinTensorStageWords, generatedNinthLowerSpinTensorStageWords10]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete source column using all original signed whole words.
private theorem column_23 : ∀ a : Fin 256, generatedNinthLowerSpinPackedHighPair10Pair01Condition 23 a := by
  dsimp only [generatedNinthLowerSpinPackedHighPair10Pair01Condition, generatedNinthLowerSpinPackedHighPair10Pair01Sources,
    generatedNinthLowerSpinPackedHighSources, generatedNinthLowerSpinPackedHighPair10Pair01Word,
    generatedNinthLowerSpinTensorStageWords, generatedNinthLowerSpinTensorStageWords10]
  decide +kernel

/-- Every original source prefix satisfies the complete signed-word certificate. -/
theorem generatedNinth_lower_spin_packed_high_pair10_pair01_certificate : ∀ j : Fin 24, ∀ a : Fin 256,
    generatedNinthLowerSpinPackedHighPair10Pair01Condition j a := by
  intro j
  fin_cases j
  · exact column_00
  · exact column_01
  · exact column_02
  · exact column_03
  · exact column_04
  · exact column_05
  · exact column_06
  · exact column_07
  · exact column_08
  · exact column_09
  · exact column_10
  · exact column_11
  · exact column_12
  · exact column_13
  · exact column_14
  · exact column_15
  · exact column_16
  · exact column_17
  · exact column_18
  · exact column_19
  · exact column_20
  · exact column_21
  · exact column_22
  · exact column_23

/-- The word certificate implies every original signed coordinate equation. -/
theorem generatedNinth_lower_spin_packed_high_pair10_pair01_signed_coordinates (j : Fin 24) (a : Fin 256) :
    ∀ i : Fin 16, (∑ z : Fin 4, generatedNinthLowerSpinPackedHighPair10Pair01Coefficients a z *
      generatedRootEightPackedSignedDigit (generatedNinthLowerSpinPackedHighPair10Pair01Sources j a z) i) =
        2 * generatedRootEightPackedSignedDigit (generatedNinthLowerSpinPackedHighPair10Pair01Word 2 j a) i := by
  have hb : ∀ b : Fin 256, generatedNinthLowerSpinPackedHighPair10Pair01Word 1 j b < 512 ^ 16 :=
    fun b => (generatedNinth_lower_spin_packed_high_pair10_pair01_certificate j b).1
  have hg : ∀ b : Fin 256,
      generatedNinthLowerSpinPackedHighPair10Pair01Word 1 j b &&& generatedRootEightPackedGapEightMask = 0 :=
    fun b => (generatedNinth_lower_spin_packed_high_pair10_pair01_certificate j b).2.2.1
  have h := generatedNinth_lower_spin_packed_high_pair10_pair01_certificate j a
  apply generatedRootEight_packed_signed_four_terms (generatedNinthLowerSpinPackedHighPair10Pair01Sources j a)
    (generatedNinthLowerSpinPackedHighPair10Pair01Word 2 j a) (generatedNinthLowerSpinPackedHighPair10Pair01Coefficients a)
  · intro z
    fin_cases z
    all_goals dsimp [generatedNinthLowerSpinPackedHighPair10Pair01Coefficients,
      generatedNinthLowerSpinPackedHighCoefficients]
    all_goals try split_ifs
    all_goals norm_num
  · intro z
    fin_cases z <;> exact hb _
  · exact h.2.1
  · intro z
    fin_cases z <;> exact hg _
  · exact h.2.2.2.1
  · exact h.2.2.2.2

/-- Every original actual Fourier coordinate follows from the complete word checks. -/
theorem generatedNinth_lower_spin_packed_high_pair10_pair01_actual_fourier (j : Fin 24) : ∀ n : Fin 4096,
    generatedNinthLowerSpinTensorFourierInteger 6
      (generatedNinthLowerSpinTensorFourierInteger 7
        (fun m => generatedNinthLowerSpinTensorStageInteger 10 1 m j)) n =
          2 * generatedNinthLowerSpinTensorStageInteger 10 2 n j := by
  change ∀ n : Fin 4096,
    generatedNinthLowerSpinTensorFourierInteger (generatedNinthLowerSpinPackedHighBit 2)
      (generatedNinthLowerSpinTensorFourierInteger (generatedNinthLowerSpinPackedHighBit 3)
        (generatedNinthLowerSpinTensorPackedCoordinate
          (generatedNinthLowerSpinTensorStageWords 10 1 j))) n =
      2 * generatedNinthLowerSpinTensorPackedCoordinate
        (generatedNinthLowerSpinTensorStageWords 10 2 j) n
  apply generatedNinth_lower_spin_packed_high_pair_of_coordinates
    (generatedNinthLowerSpinTensorStageWords 10 1 j)
    (generatedNinthLowerSpinTensorStageWords 10 2 j) 2 3 (by decide)
  intro a i
  exact generatedNinth_lower_spin_packed_high_pair10_pair01_signed_coordinates j a i

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
