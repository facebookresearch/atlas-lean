/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinPackedHighPairGeneric
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryPackedCandidate10Stage03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryPackedCandidate10Stage04

/-! Complete original candidate10 paired Fourier step3. All24columns and4096coordinates remain
  covered. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

/-- One complete source stage word, retaining the entire original prefix. -/
def generatedTenthTenStageThreeToFourPairWord (stage : ℕ) (j : Fin 24) (a : Fin
  256) : ℕ :=
  (if stage = 3 then generatedTenthAxisLowerRecoveryPackedCandidate10Stage03Words j else
    generatedTenthAxisLowerRecoveryPackedCandidate10Stage04Words j)
    ⟨a.val / 16, by omega⟩ ⟨a.val % 16, Nat.mod_lt _ (by decide)⟩

/-- Toggling a genuine Fourier bit in the complete original word prefix. -/
def generatedTenthTenStageThreeToFourPairXor :=
  generatedNinthLowerSpinPackedPrefixXor

/-- Four original source words in the order of the paired Fourier expansion. -/
def generatedTenthTenStageThreeToFourPairSources (j : Fin 24) (a : Fin 256) : Fin
  4 → ℕ :=
  generatedNinthLowerSpinPackedHighSources
    (generatedTenthTenStageThreeToFourPairWord 3 j) 2 3 a

/-- The complete original paired Fourier signs. -/
def generatedTenthTenStageThreeToFourPairCoefficients (a : Fin 256) : Fin 4 → ℤ :=
  generatedNinthLowerSpinPackedHighCoefficients 2 3 a

/-- Range and low-bit certificates refer to both complete original source stages. -/
def generatedTenthTenStageThreeToFourPairCondition (j : Fin 24) (a : Fin 256) : Prop :=
  generatedTenthTenStageThreeToFourPairWord 3 j a < 512 ^ 16 ∧
  generatedTenthTenStageThreeToFourPairWord 4 j a < 512 ^ 16 ∧
  generatedTenthTenStageThreeToFourPairWord 3 j a &&& generatedRootEightPackedGapEightMask = 0 ∧
  generatedTenthTenStageThreeToFourPairWord 4 j a &&& generatedRootEightPackedGapEightMask = 0 ∧
  (∑ z : Fin 4, generatedTenthTenStageThreeToFourPairCoefficients a z *
    generatedRootEightPackedSignedWord
      (generatedTenthTenStageThreeToFourPairSources j a z)) =
      2 * generatedRootEightPackedSignedWord (generatedTenthTenStageThreeToFourPairWord 4 j a)

set_option maxHeartbeats 8000000 in
-- Check one complete source column using all original signed whole words.
private theorem column_00 : ∀ a : Fin 256,
  generatedTenthTenStageThreeToFourPairCondition 0 a := by
  dsimp only [generatedTenthTenStageThreeToFourPairCondition,
    generatedTenthTenStageThreeToFourPairSources,
    generatedNinthLowerSpinPackedHighSources,
      generatedTenthTenStageThreeToFourPairWord,
    generatedTenthAxisLowerRecoveryPackedCandidate10Stage03Words,
      generatedTenthAxisLowerRecoveryPackedCandidate10Stage04Words]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete source column using all original signed whole words.
private theorem column_01 : ∀ a : Fin 256,
  generatedTenthTenStageThreeToFourPairCondition 1 a := by
  dsimp only [generatedTenthTenStageThreeToFourPairCondition,
    generatedTenthTenStageThreeToFourPairSources,
    generatedNinthLowerSpinPackedHighSources,
      generatedTenthTenStageThreeToFourPairWord,
    generatedTenthAxisLowerRecoveryPackedCandidate10Stage03Words,
      generatedTenthAxisLowerRecoveryPackedCandidate10Stage04Words]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete source column using all original signed whole words.
private theorem column_02 : ∀ a : Fin 256,
  generatedTenthTenStageThreeToFourPairCondition 2 a := by
  dsimp only [generatedTenthTenStageThreeToFourPairCondition,
    generatedTenthTenStageThreeToFourPairSources,
    generatedNinthLowerSpinPackedHighSources,
      generatedTenthTenStageThreeToFourPairWord,
    generatedTenthAxisLowerRecoveryPackedCandidate10Stage03Words,
      generatedTenthAxisLowerRecoveryPackedCandidate10Stage04Words]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete source column using all original signed whole words.
private theorem column_03 : ∀ a : Fin 256,
  generatedTenthTenStageThreeToFourPairCondition 3 a := by
  dsimp only [generatedTenthTenStageThreeToFourPairCondition,
    generatedTenthTenStageThreeToFourPairSources,
    generatedNinthLowerSpinPackedHighSources,
      generatedTenthTenStageThreeToFourPairWord,
    generatedTenthAxisLowerRecoveryPackedCandidate10Stage03Words,
      generatedTenthAxisLowerRecoveryPackedCandidate10Stage04Words]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete source column using all original signed whole words.
private theorem column_04 : ∀ a : Fin 256,
  generatedTenthTenStageThreeToFourPairCondition 4 a := by
  dsimp only [generatedTenthTenStageThreeToFourPairCondition,
    generatedTenthTenStageThreeToFourPairSources,
    generatedNinthLowerSpinPackedHighSources,
      generatedTenthTenStageThreeToFourPairWord,
    generatedTenthAxisLowerRecoveryPackedCandidate10Stage03Words,
      generatedTenthAxisLowerRecoveryPackedCandidate10Stage04Words]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete source column using all original signed whole words.
private theorem column_05 : ∀ a : Fin 256,
  generatedTenthTenStageThreeToFourPairCondition 5 a := by
  dsimp only [generatedTenthTenStageThreeToFourPairCondition,
    generatedTenthTenStageThreeToFourPairSources,
    generatedNinthLowerSpinPackedHighSources,
      generatedTenthTenStageThreeToFourPairWord,
    generatedTenthAxisLowerRecoveryPackedCandidate10Stage03Words,
      generatedTenthAxisLowerRecoveryPackedCandidate10Stage04Words]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete source column using all original signed whole words.
private theorem column_06 : ∀ a : Fin 256,
  generatedTenthTenStageThreeToFourPairCondition 6 a := by
  dsimp only [generatedTenthTenStageThreeToFourPairCondition,
    generatedTenthTenStageThreeToFourPairSources,
    generatedNinthLowerSpinPackedHighSources,
      generatedTenthTenStageThreeToFourPairWord,
    generatedTenthAxisLowerRecoveryPackedCandidate10Stage03Words,
      generatedTenthAxisLowerRecoveryPackedCandidate10Stage04Words]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete source column using all original signed whole words.
private theorem column_07 : ∀ a : Fin 256,
  generatedTenthTenStageThreeToFourPairCondition 7 a := by
  dsimp only [generatedTenthTenStageThreeToFourPairCondition,
    generatedTenthTenStageThreeToFourPairSources,
    generatedNinthLowerSpinPackedHighSources,
      generatedTenthTenStageThreeToFourPairWord,
    generatedTenthAxisLowerRecoveryPackedCandidate10Stage03Words,
      generatedTenthAxisLowerRecoveryPackedCandidate10Stage04Words]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete source column using all original signed whole words.
private theorem column_08 : ∀ a : Fin 256,
  generatedTenthTenStageThreeToFourPairCondition 8 a := by
  dsimp only [generatedTenthTenStageThreeToFourPairCondition,
    generatedTenthTenStageThreeToFourPairSources,
    generatedNinthLowerSpinPackedHighSources,
      generatedTenthTenStageThreeToFourPairWord,
    generatedTenthAxisLowerRecoveryPackedCandidate10Stage03Words,
      generatedTenthAxisLowerRecoveryPackedCandidate10Stage04Words]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete source column using all original signed whole words.
private theorem column_09 : ∀ a : Fin 256,
  generatedTenthTenStageThreeToFourPairCondition 9 a := by
  dsimp only [generatedTenthTenStageThreeToFourPairCondition,
    generatedTenthTenStageThreeToFourPairSources,
    generatedNinthLowerSpinPackedHighSources,
      generatedTenthTenStageThreeToFourPairWord,
    generatedTenthAxisLowerRecoveryPackedCandidate10Stage03Words,
      generatedTenthAxisLowerRecoveryPackedCandidate10Stage04Words]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete source column using all original signed whole words.
private theorem column_10 : ∀ a : Fin 256,
  generatedTenthTenStageThreeToFourPairCondition 10 a := by
  dsimp only [generatedTenthTenStageThreeToFourPairCondition,
    generatedTenthTenStageThreeToFourPairSources,
    generatedNinthLowerSpinPackedHighSources,
      generatedTenthTenStageThreeToFourPairWord,
    generatedTenthAxisLowerRecoveryPackedCandidate10Stage03Words,
      generatedTenthAxisLowerRecoveryPackedCandidate10Stage04Words]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete source column using all original signed whole words.
private theorem column_11 : ∀ a : Fin 256,
  generatedTenthTenStageThreeToFourPairCondition 11 a := by
  dsimp only [generatedTenthTenStageThreeToFourPairCondition,
    generatedTenthTenStageThreeToFourPairSources,
    generatedNinthLowerSpinPackedHighSources,
      generatedTenthTenStageThreeToFourPairWord,
    generatedTenthAxisLowerRecoveryPackedCandidate10Stage03Words,
      generatedTenthAxisLowerRecoveryPackedCandidate10Stage04Words]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete source column using all original signed whole words.
private theorem column_12 : ∀ a : Fin 256,
  generatedTenthTenStageThreeToFourPairCondition 12 a := by
  dsimp only [generatedTenthTenStageThreeToFourPairCondition,
    generatedTenthTenStageThreeToFourPairSources,
    generatedNinthLowerSpinPackedHighSources,
      generatedTenthTenStageThreeToFourPairWord,
    generatedTenthAxisLowerRecoveryPackedCandidate10Stage03Words,
      generatedTenthAxisLowerRecoveryPackedCandidate10Stage04Words]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete source column using all original signed whole words.
private theorem column_13 : ∀ a : Fin 256,
  generatedTenthTenStageThreeToFourPairCondition 13 a := by
  dsimp only [generatedTenthTenStageThreeToFourPairCondition,
    generatedTenthTenStageThreeToFourPairSources,
    generatedNinthLowerSpinPackedHighSources,
      generatedTenthTenStageThreeToFourPairWord,
    generatedTenthAxisLowerRecoveryPackedCandidate10Stage03Words,
      generatedTenthAxisLowerRecoveryPackedCandidate10Stage04Words]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete source column using all original signed whole words.
private theorem column_14 : ∀ a : Fin 256,
  generatedTenthTenStageThreeToFourPairCondition 14 a := by
  dsimp only [generatedTenthTenStageThreeToFourPairCondition,
    generatedTenthTenStageThreeToFourPairSources,
    generatedNinthLowerSpinPackedHighSources,
      generatedTenthTenStageThreeToFourPairWord,
    generatedTenthAxisLowerRecoveryPackedCandidate10Stage03Words,
      generatedTenthAxisLowerRecoveryPackedCandidate10Stage04Words]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete source column using all original signed whole words.
private theorem column_15 : ∀ a : Fin 256,
  generatedTenthTenStageThreeToFourPairCondition 15 a := by
  dsimp only [generatedTenthTenStageThreeToFourPairCondition,
    generatedTenthTenStageThreeToFourPairSources,
    generatedNinthLowerSpinPackedHighSources,
      generatedTenthTenStageThreeToFourPairWord,
    generatedTenthAxisLowerRecoveryPackedCandidate10Stage03Words,
      generatedTenthAxisLowerRecoveryPackedCandidate10Stage04Words]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete source column using all original signed whole words.
private theorem column_16 : ∀ a : Fin 256,
  generatedTenthTenStageThreeToFourPairCondition 16 a := by
  dsimp only [generatedTenthTenStageThreeToFourPairCondition,
    generatedTenthTenStageThreeToFourPairSources,
    generatedNinthLowerSpinPackedHighSources,
      generatedTenthTenStageThreeToFourPairWord,
    generatedTenthAxisLowerRecoveryPackedCandidate10Stage03Words,
      generatedTenthAxisLowerRecoveryPackedCandidate10Stage04Words]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete source column using all original signed whole words.
private theorem column_17 : ∀ a : Fin 256,
  generatedTenthTenStageThreeToFourPairCondition 17 a := by
  dsimp only [generatedTenthTenStageThreeToFourPairCondition,
    generatedTenthTenStageThreeToFourPairSources,
    generatedNinthLowerSpinPackedHighSources,
      generatedTenthTenStageThreeToFourPairWord,
    generatedTenthAxisLowerRecoveryPackedCandidate10Stage03Words,
      generatedTenthAxisLowerRecoveryPackedCandidate10Stage04Words]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete source column using all original signed whole words.
private theorem column_18 : ∀ a : Fin 256,
  generatedTenthTenStageThreeToFourPairCondition 18 a := by
  dsimp only [generatedTenthTenStageThreeToFourPairCondition,
    generatedTenthTenStageThreeToFourPairSources,
    generatedNinthLowerSpinPackedHighSources,
      generatedTenthTenStageThreeToFourPairWord,
    generatedTenthAxisLowerRecoveryPackedCandidate10Stage03Words,
      generatedTenthAxisLowerRecoveryPackedCandidate10Stage04Words]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete source column using all original signed whole words.
private theorem column_19 : ∀ a : Fin 256,
  generatedTenthTenStageThreeToFourPairCondition 19 a := by
  dsimp only [generatedTenthTenStageThreeToFourPairCondition,
    generatedTenthTenStageThreeToFourPairSources,
    generatedNinthLowerSpinPackedHighSources,
      generatedTenthTenStageThreeToFourPairWord,
    generatedTenthAxisLowerRecoveryPackedCandidate10Stage03Words,
      generatedTenthAxisLowerRecoveryPackedCandidate10Stage04Words]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete source column using all original signed whole words.
private theorem column_20 : ∀ a : Fin 256,
  generatedTenthTenStageThreeToFourPairCondition 20 a := by
  dsimp only [generatedTenthTenStageThreeToFourPairCondition,
    generatedTenthTenStageThreeToFourPairSources,
    generatedNinthLowerSpinPackedHighSources,
      generatedTenthTenStageThreeToFourPairWord,
    generatedTenthAxisLowerRecoveryPackedCandidate10Stage03Words,
      generatedTenthAxisLowerRecoveryPackedCandidate10Stage04Words]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete source column using all original signed whole words.
private theorem column_21 : ∀ a : Fin 256,
  generatedTenthTenStageThreeToFourPairCondition 21 a := by
  dsimp only [generatedTenthTenStageThreeToFourPairCondition,
    generatedTenthTenStageThreeToFourPairSources,
    generatedNinthLowerSpinPackedHighSources,
      generatedTenthTenStageThreeToFourPairWord,
    generatedTenthAxisLowerRecoveryPackedCandidate10Stage03Words,
      generatedTenthAxisLowerRecoveryPackedCandidate10Stage04Words]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete source column using all original signed whole words.
private theorem column_22 : ∀ a : Fin 256,
  generatedTenthTenStageThreeToFourPairCondition 22 a := by
  dsimp only [generatedTenthTenStageThreeToFourPairCondition,
    generatedTenthTenStageThreeToFourPairSources,
    generatedNinthLowerSpinPackedHighSources,
      generatedTenthTenStageThreeToFourPairWord,
    generatedTenthAxisLowerRecoveryPackedCandidate10Stage03Words,
      generatedTenthAxisLowerRecoveryPackedCandidate10Stage04Words]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete source column using all original signed whole words.
private theorem column_23 : ∀ a : Fin 256,
  generatedTenthTenStageThreeToFourPairCondition 23 a := by
  dsimp only [generatedTenthTenStageThreeToFourPairCondition,
    generatedTenthTenStageThreeToFourPairSources,
    generatedNinthLowerSpinPackedHighSources,
      generatedTenthTenStageThreeToFourPairWord,
    generatedTenthAxisLowerRecoveryPackedCandidate10Stage03Words,
      generatedTenthAxisLowerRecoveryPackedCandidate10Stage04Words]
  decide +kernel

/-- Every original source prefix satisfies the complete signed-word certificate. -/
theorem generatedTenth_candidate_ten_stage_three_to_four_certificate : ∀ j : Fin 24, ∀
  a : Fin 256,
    generatedTenthTenStageThreeToFourPairCondition j a := by
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
theorem generatedTenth_candidate_ten_stage_three_to_four_signed_coordinates (j : Fin
  24) (a : Fin 256) :
    ∀ i : Fin 16, (∑ z : Fin 4, generatedTenthTenStageThreeToFourPairCoefficients
      a z *
      generatedRootEightPackedSignedDigit
        (generatedTenthTenStageThreeToFourPairSources j a z) i) =
        2 * generatedRootEightPackedSignedDigit
          (generatedTenthTenStageThreeToFourPairWord 4 j a) i := by
  have hb : ∀ b : Fin 256, generatedTenthTenStageThreeToFourPairWord 3 j b < 512
    ^ 16 :=
    fun b => (generatedTenth_candidate_ten_stage_three_to_four_certificate j b).1
  have hg : ∀ b : Fin 256,
      generatedTenthTenStageThreeToFourPairWord 3 j b &&&
        generatedRootEightPackedGapEightMask = 0 :=
    fun b => (generatedTenth_candidate_ten_stage_three_to_four_certificate j b).2.2.1
  have h := generatedTenth_candidate_ten_stage_three_to_four_certificate j a
  apply generatedRootEight_packed_signed_four_terms
    (generatedTenthTenStageThreeToFourPairSources j a)
    (generatedTenthTenStageThreeToFourPairWord 4 j a)
      (generatedTenthTenStageThreeToFourPairCoefficients a)
  · intro z
    fin_cases z
    all_goals dsimp [generatedTenthTenStageThreeToFourPairCoefficients,
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
theorem generatedTenth_axis_lower_recovery_packed_candidate10_pair03_actual_fourier (j : Fin 24) :
  ∀ n : Fin 4096,
    generatedNinthLowerSpinTensorFourierInteger 6
      (generatedNinthLowerSpinTensorFourierInteger 7
        (fun m => generatedNinthLowerSpinTensorPackedCoordinate
          (generatedTenthAxisLowerRecoveryPackedCandidate10Stage03Words j) m)) n =
          2 * generatedNinthLowerSpinTensorPackedCoordinate
            (generatedTenthAxisLowerRecoveryPackedCandidate10Stage04Words j) n := by
  change ∀ n : Fin 4096,
    generatedNinthLowerSpinTensorFourierInteger (generatedNinthLowerSpinPackedHighBit 2)
      (generatedNinthLowerSpinTensorFourierInteger (generatedNinthLowerSpinPackedHighBit 3)
        (generatedNinthLowerSpinTensorPackedCoordinate
          (generatedTenthAxisLowerRecoveryPackedCandidate10Stage03Words j))) n =
      2 * generatedNinthLowerSpinTensorPackedCoordinate
        (generatedTenthAxisLowerRecoveryPackedCandidate10Stage04Words j) n
  apply generatedNinth_lower_spin_packed_high_pair_of_coordinates
    (generatedTenthAxisLowerRecoveryPackedCandidate10Stage03Words j)
    (generatedTenthAxisLowerRecoveryPackedCandidate10Stage04Words j) 2 3 (by decide)
  intro a i
  exact generatedTenth_candidate_ten_stage_three_to_four_signed_coordinates j a i

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
