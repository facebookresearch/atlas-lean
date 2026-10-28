/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinPackedHighPairGeneric
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryJointPackedStage04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryJointPackedStage05

/-! Complete original joint9*1 paired Fourier step4. All24columns and4096coordinates remain covered.
  -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option maxRecDepth 100000

/-- One complete source stage word, retaining the entire original prefix. -/
def generatedTenthAxisLowerRecoveryJointPackedPair04Word (stage : ℕ) (j : Fin 24) (a : Fin
  256) : ℕ :=
  (if stage = 4 then generatedTenthAxisLowerRecoveryJointPackedStage04Words j else
    generatedTenthAxisLowerRecoveryJointPackedStage05Words j)
    ⟨a.val / 16, by omega⟩ ⟨a.val % 16, Nat.mod_lt _ (by decide)⟩

/-- Toggling a genuine Fourier bit in the complete original word prefix. -/
def generatedTenthAxisLowerRecoveryJointPackedPair04Xor :=
  generatedNinthLowerSpinPackedPrefixXor

/-- Four original source words in the order of the paired Fourier expansion. -/
def generatedTenthAxisLowerRecoveryJointPackedPair04Sources (j : Fin 24) (a : Fin 256) : Fin
  4 → ℕ :=
  generatedNinthLowerSpinPackedHighSources
    (generatedTenthAxisLowerRecoveryJointPackedPair04Word 4 j) 4 5 a

/-- The complete original paired Fourier signs. -/
def generatedTenthAxisLowerRecoveryJointPackedPair04Coefficients (a : Fin 256) : Fin 4 → ℤ :=
  generatedNinthLowerSpinPackedHighCoefficients 4 5 a

/-- Range and low-bit certificates refer to both complete original source stages. -/
def generatedTenthAxisLowerRecoveryJointPackedPair04Condition (j : Fin 24) (a : Fin 256) :
  Prop :=
  generatedTenthAxisLowerRecoveryJointPackedPair04Word 4 j a < 512 ^ 16 ∧
  generatedTenthAxisLowerRecoveryJointPackedPair04Word 5 j a < 512 ^ 16 ∧
  generatedTenthAxisLowerRecoveryJointPackedPair04Word 4 j a &&&
    generatedRootEightPackedGapEightMask = 0 ∧
  generatedTenthAxisLowerRecoveryJointPackedPair04Word 5 j a &&&
    generatedRootEightPackedGapEightMask = 0 ∧
  (∑ z : Fin 4, generatedTenthAxisLowerRecoveryJointPackedPair04Coefficients a z *
    generatedRootEightPackedSignedWord
      (generatedTenthAxisLowerRecoveryJointPackedPair04Sources j a z)) =
      2 * generatedRootEightPackedSignedWord
        (generatedTenthAxisLowerRecoveryJointPackedPair04Word 5 j a)

set_option maxHeartbeats 8000000 in
-- Check one complete source column using all original signed whole words.
private theorem column_00 : ∀ a : Fin 256,
  generatedTenthAxisLowerRecoveryJointPackedPair04Condition 0 a := by
  dsimp only [generatedTenthAxisLowerRecoveryJointPackedPair04Condition,
    generatedTenthAxisLowerRecoveryJointPackedPair04Sources,
    generatedNinthLowerSpinPackedHighSources,
      generatedTenthAxisLowerRecoveryJointPackedPair04Word,
    generatedTenthAxisLowerRecoveryJointPackedStage04Words,
      generatedTenthAxisLowerRecoveryJointPackedStage05Words]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete source column using all original signed whole words.
private theorem column_01 : ∀ a : Fin 256,
  generatedTenthAxisLowerRecoveryJointPackedPair04Condition 1 a := by
  dsimp only [generatedTenthAxisLowerRecoveryJointPackedPair04Condition,
    generatedTenthAxisLowerRecoveryJointPackedPair04Sources,
    generatedNinthLowerSpinPackedHighSources,
      generatedTenthAxisLowerRecoveryJointPackedPair04Word,
    generatedTenthAxisLowerRecoveryJointPackedStage04Words,
      generatedTenthAxisLowerRecoveryJointPackedStage05Words]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete source column using all original signed whole words.
private theorem column_02 : ∀ a : Fin 256,
  generatedTenthAxisLowerRecoveryJointPackedPair04Condition 2 a := by
  dsimp only [generatedTenthAxisLowerRecoveryJointPackedPair04Condition,
    generatedTenthAxisLowerRecoveryJointPackedPair04Sources,
    generatedNinthLowerSpinPackedHighSources,
      generatedTenthAxisLowerRecoveryJointPackedPair04Word,
    generatedTenthAxisLowerRecoveryJointPackedStage04Words,
      generatedTenthAxisLowerRecoveryJointPackedStage05Words]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete source column using all original signed whole words.
private theorem column_03 : ∀ a : Fin 256,
  generatedTenthAxisLowerRecoveryJointPackedPair04Condition 3 a := by
  dsimp only [generatedTenthAxisLowerRecoveryJointPackedPair04Condition,
    generatedTenthAxisLowerRecoveryJointPackedPair04Sources,
    generatedNinthLowerSpinPackedHighSources,
      generatedTenthAxisLowerRecoveryJointPackedPair04Word,
    generatedTenthAxisLowerRecoveryJointPackedStage04Words,
      generatedTenthAxisLowerRecoveryJointPackedStage05Words]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete source column using all original signed whole words.
private theorem column_04 : ∀ a : Fin 256,
  generatedTenthAxisLowerRecoveryJointPackedPair04Condition 4 a := by
  dsimp only [generatedTenthAxisLowerRecoveryJointPackedPair04Condition,
    generatedTenthAxisLowerRecoveryJointPackedPair04Sources,
    generatedNinthLowerSpinPackedHighSources,
      generatedTenthAxisLowerRecoveryJointPackedPair04Word,
    generatedTenthAxisLowerRecoveryJointPackedStage04Words,
      generatedTenthAxisLowerRecoveryJointPackedStage05Words]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete source column using all original signed whole words.
private theorem column_05 : ∀ a : Fin 256,
  generatedTenthAxisLowerRecoveryJointPackedPair04Condition 5 a := by
  dsimp only [generatedTenthAxisLowerRecoveryJointPackedPair04Condition,
    generatedTenthAxisLowerRecoveryJointPackedPair04Sources,
    generatedNinthLowerSpinPackedHighSources,
      generatedTenthAxisLowerRecoveryJointPackedPair04Word,
    generatedTenthAxisLowerRecoveryJointPackedStage04Words,
      generatedTenthAxisLowerRecoveryJointPackedStage05Words]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete source column using all original signed whole words.
private theorem column_06 : ∀ a : Fin 256,
  generatedTenthAxisLowerRecoveryJointPackedPair04Condition 6 a := by
  dsimp only [generatedTenthAxisLowerRecoveryJointPackedPair04Condition,
    generatedTenthAxisLowerRecoveryJointPackedPair04Sources,
    generatedNinthLowerSpinPackedHighSources,
      generatedTenthAxisLowerRecoveryJointPackedPair04Word,
    generatedTenthAxisLowerRecoveryJointPackedStage04Words,
      generatedTenthAxisLowerRecoveryJointPackedStage05Words]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete source column using all original signed whole words.
private theorem column_07 : ∀ a : Fin 256,
  generatedTenthAxisLowerRecoveryJointPackedPair04Condition 7 a := by
  dsimp only [generatedTenthAxisLowerRecoveryJointPackedPair04Condition,
    generatedTenthAxisLowerRecoveryJointPackedPair04Sources,
    generatedNinthLowerSpinPackedHighSources,
      generatedTenthAxisLowerRecoveryJointPackedPair04Word,
    generatedTenthAxisLowerRecoveryJointPackedStage04Words,
      generatedTenthAxisLowerRecoveryJointPackedStage05Words]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete source column using all original signed whole words.
private theorem column_08 : ∀ a : Fin 256,
  generatedTenthAxisLowerRecoveryJointPackedPair04Condition 8 a := by
  dsimp only [generatedTenthAxisLowerRecoveryJointPackedPair04Condition,
    generatedTenthAxisLowerRecoveryJointPackedPair04Sources,
    generatedNinthLowerSpinPackedHighSources,
      generatedTenthAxisLowerRecoveryJointPackedPair04Word,
    generatedTenthAxisLowerRecoveryJointPackedStage04Words,
      generatedTenthAxisLowerRecoveryJointPackedStage05Words]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete source column using all original signed whole words.
private theorem column_09 : ∀ a : Fin 256,
  generatedTenthAxisLowerRecoveryJointPackedPair04Condition 9 a := by
  dsimp only [generatedTenthAxisLowerRecoveryJointPackedPair04Condition,
    generatedTenthAxisLowerRecoveryJointPackedPair04Sources,
    generatedNinthLowerSpinPackedHighSources,
      generatedTenthAxisLowerRecoveryJointPackedPair04Word,
    generatedTenthAxisLowerRecoveryJointPackedStage04Words,
      generatedTenthAxisLowerRecoveryJointPackedStage05Words]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete source column using all original signed whole words.
private theorem column_10 : ∀ a : Fin 256,
  generatedTenthAxisLowerRecoveryJointPackedPair04Condition 10 a := by
  dsimp only [generatedTenthAxisLowerRecoveryJointPackedPair04Condition,
    generatedTenthAxisLowerRecoveryJointPackedPair04Sources,
    generatedNinthLowerSpinPackedHighSources,
      generatedTenthAxisLowerRecoveryJointPackedPair04Word,
    generatedTenthAxisLowerRecoveryJointPackedStage04Words,
      generatedTenthAxisLowerRecoveryJointPackedStage05Words]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete source column using all original signed whole words.
private theorem column_11 : ∀ a : Fin 256,
  generatedTenthAxisLowerRecoveryJointPackedPair04Condition 11 a := by
  dsimp only [generatedTenthAxisLowerRecoveryJointPackedPair04Condition,
    generatedTenthAxisLowerRecoveryJointPackedPair04Sources,
    generatedNinthLowerSpinPackedHighSources,
      generatedTenthAxisLowerRecoveryJointPackedPair04Word,
    generatedTenthAxisLowerRecoveryJointPackedStage04Words,
      generatedTenthAxisLowerRecoveryJointPackedStage05Words]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete source column using all original signed whole words.
private theorem column_12 : ∀ a : Fin 256,
  generatedTenthAxisLowerRecoveryJointPackedPair04Condition 12 a := by
  dsimp only [generatedTenthAxisLowerRecoveryJointPackedPair04Condition,
    generatedTenthAxisLowerRecoveryJointPackedPair04Sources,
    generatedNinthLowerSpinPackedHighSources,
      generatedTenthAxisLowerRecoveryJointPackedPair04Word,
    generatedTenthAxisLowerRecoveryJointPackedStage04Words,
      generatedTenthAxisLowerRecoveryJointPackedStage05Words]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete source column using all original signed whole words.
private theorem column_13 : ∀ a : Fin 256,
  generatedTenthAxisLowerRecoveryJointPackedPair04Condition 13 a := by
  dsimp only [generatedTenthAxisLowerRecoveryJointPackedPair04Condition,
    generatedTenthAxisLowerRecoveryJointPackedPair04Sources,
    generatedNinthLowerSpinPackedHighSources,
      generatedTenthAxisLowerRecoveryJointPackedPair04Word,
    generatedTenthAxisLowerRecoveryJointPackedStage04Words,
      generatedTenthAxisLowerRecoveryJointPackedStage05Words]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete source column using all original signed whole words.
private theorem column_14 : ∀ a : Fin 256,
  generatedTenthAxisLowerRecoveryJointPackedPair04Condition 14 a := by
  dsimp only [generatedTenthAxisLowerRecoveryJointPackedPair04Condition,
    generatedTenthAxisLowerRecoveryJointPackedPair04Sources,
    generatedNinthLowerSpinPackedHighSources,
      generatedTenthAxisLowerRecoveryJointPackedPair04Word,
    generatedTenthAxisLowerRecoveryJointPackedStage04Words,
      generatedTenthAxisLowerRecoveryJointPackedStage05Words]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete source column using all original signed whole words.
private theorem column_15 : ∀ a : Fin 256,
  generatedTenthAxisLowerRecoveryJointPackedPair04Condition 15 a := by
  dsimp only [generatedTenthAxisLowerRecoveryJointPackedPair04Condition,
    generatedTenthAxisLowerRecoveryJointPackedPair04Sources,
    generatedNinthLowerSpinPackedHighSources,
      generatedTenthAxisLowerRecoveryJointPackedPair04Word,
    generatedTenthAxisLowerRecoveryJointPackedStage04Words,
      generatedTenthAxisLowerRecoveryJointPackedStage05Words]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete source column using all original signed whole words.
private theorem column_16 : ∀ a : Fin 256,
  generatedTenthAxisLowerRecoveryJointPackedPair04Condition 16 a := by
  dsimp only [generatedTenthAxisLowerRecoveryJointPackedPair04Condition,
    generatedTenthAxisLowerRecoveryJointPackedPair04Sources,
    generatedNinthLowerSpinPackedHighSources,
      generatedTenthAxisLowerRecoveryJointPackedPair04Word,
    generatedTenthAxisLowerRecoveryJointPackedStage04Words,
      generatedTenthAxisLowerRecoveryJointPackedStage05Words]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete source column using all original signed whole words.
private theorem column_17 : ∀ a : Fin 256,
  generatedTenthAxisLowerRecoveryJointPackedPair04Condition 17 a := by
  dsimp only [generatedTenthAxisLowerRecoveryJointPackedPair04Condition,
    generatedTenthAxisLowerRecoveryJointPackedPair04Sources,
    generatedNinthLowerSpinPackedHighSources,
      generatedTenthAxisLowerRecoveryJointPackedPair04Word,
    generatedTenthAxisLowerRecoveryJointPackedStage04Words,
      generatedTenthAxisLowerRecoveryJointPackedStage05Words]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete source column using all original signed whole words.
private theorem column_18 : ∀ a : Fin 256,
  generatedTenthAxisLowerRecoveryJointPackedPair04Condition 18 a := by
  dsimp only [generatedTenthAxisLowerRecoveryJointPackedPair04Condition,
    generatedTenthAxisLowerRecoveryJointPackedPair04Sources,
    generatedNinthLowerSpinPackedHighSources,
      generatedTenthAxisLowerRecoveryJointPackedPair04Word,
    generatedTenthAxisLowerRecoveryJointPackedStage04Words,
      generatedTenthAxisLowerRecoveryJointPackedStage05Words]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete source column using all original signed whole words.
private theorem column_19 : ∀ a : Fin 256,
  generatedTenthAxisLowerRecoveryJointPackedPair04Condition 19 a := by
  dsimp only [generatedTenthAxisLowerRecoveryJointPackedPair04Condition,
    generatedTenthAxisLowerRecoveryJointPackedPair04Sources,
    generatedNinthLowerSpinPackedHighSources,
      generatedTenthAxisLowerRecoveryJointPackedPair04Word,
    generatedTenthAxisLowerRecoveryJointPackedStage04Words,
      generatedTenthAxisLowerRecoveryJointPackedStage05Words]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete source column using all original signed whole words.
private theorem column_20 : ∀ a : Fin 256,
  generatedTenthAxisLowerRecoveryJointPackedPair04Condition 20 a := by
  dsimp only [generatedTenthAxisLowerRecoveryJointPackedPair04Condition,
    generatedTenthAxisLowerRecoveryJointPackedPair04Sources,
    generatedNinthLowerSpinPackedHighSources,
      generatedTenthAxisLowerRecoveryJointPackedPair04Word,
    generatedTenthAxisLowerRecoveryJointPackedStage04Words,
      generatedTenthAxisLowerRecoveryJointPackedStage05Words]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete source column using all original signed whole words.
private theorem column_21 : ∀ a : Fin 256,
  generatedTenthAxisLowerRecoveryJointPackedPair04Condition 21 a := by
  dsimp only [generatedTenthAxisLowerRecoveryJointPackedPair04Condition,
    generatedTenthAxisLowerRecoveryJointPackedPair04Sources,
    generatedNinthLowerSpinPackedHighSources,
      generatedTenthAxisLowerRecoveryJointPackedPair04Word,
    generatedTenthAxisLowerRecoveryJointPackedStage04Words,
      generatedTenthAxisLowerRecoveryJointPackedStage05Words]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete source column using all original signed whole words.
private theorem column_22 : ∀ a : Fin 256,
  generatedTenthAxisLowerRecoveryJointPackedPair04Condition 22 a := by
  dsimp only [generatedTenthAxisLowerRecoveryJointPackedPair04Condition,
    generatedTenthAxisLowerRecoveryJointPackedPair04Sources,
    generatedNinthLowerSpinPackedHighSources,
      generatedTenthAxisLowerRecoveryJointPackedPair04Word,
    generatedTenthAxisLowerRecoveryJointPackedStage04Words,
      generatedTenthAxisLowerRecoveryJointPackedStage05Words]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check one complete source column using all original signed whole words.
private theorem column_23 : ∀ a : Fin 256,
  generatedTenthAxisLowerRecoveryJointPackedPair04Condition 23 a := by
  dsimp only [generatedTenthAxisLowerRecoveryJointPackedPair04Condition,
    generatedTenthAxisLowerRecoveryJointPackedPair04Sources,
    generatedNinthLowerSpinPackedHighSources,
      generatedTenthAxisLowerRecoveryJointPackedPair04Word,
    generatedTenthAxisLowerRecoveryJointPackedStage04Words,
      generatedTenthAxisLowerRecoveryJointPackedStage05Words]
  decide +kernel

/-- Every original source prefix satisfies the complete signed-word certificate. -/
theorem generatedTenth_axis_lower_recovery_joint_packed_pair04_certificate : ∀ j : Fin 24, ∀
  a : Fin 256,
    generatedTenthAxisLowerRecoveryJointPackedPair04Condition j a := by
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
theorem generatedTenth_axis_lower_recovery_joint_packed_pair04_signed_coordinates (j : Fin
  24) (a : Fin 256) :
    ∀ i : Fin 16, (∑ z : Fin 4, generatedTenthAxisLowerRecoveryJointPackedPair04Coefficients
      a z *
      generatedRootEightPackedSignedDigit
        (generatedTenthAxisLowerRecoveryJointPackedPair04Sources j a z) i) =
        2 * generatedRootEightPackedSignedDigit
          (generatedTenthAxisLowerRecoveryJointPackedPair04Word 5 j a) i := by
  have hb : ∀ b : Fin 256, generatedTenthAxisLowerRecoveryJointPackedPair04Word 4 j b < 512
    ^ 16 :=
    fun b => (generatedTenth_axis_lower_recovery_joint_packed_pair04_certificate j b).1
  have hg : ∀ b : Fin 256,
      generatedTenthAxisLowerRecoveryJointPackedPair04Word 4 j b &&&
        generatedRootEightPackedGapEightMask = 0 :=
    fun b => (generatedTenth_axis_lower_recovery_joint_packed_pair04_certificate j b).2.2.1
  have h := generatedTenth_axis_lower_recovery_joint_packed_pair04_certificate j a
  apply generatedRootEight_packed_signed_four_terms
    (generatedTenthAxisLowerRecoveryJointPackedPair04Sources j a)
    (generatedTenthAxisLowerRecoveryJointPackedPair04Word 5 j a)
      (generatedTenthAxisLowerRecoveryJointPackedPair04Coefficients a)
  · intro z
    fin_cases z
    all_goals dsimp [generatedTenthAxisLowerRecoveryJointPackedPair04Coefficients,
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
theorem generatedTenth_axis_lower_recovery_joint_packed_pair04_actual_fourier (j : Fin 24) :
  ∀ n : Fin 4096,
    generatedNinthLowerSpinTensorFourierInteger 8
      (generatedNinthLowerSpinTensorFourierInteger 9
        (fun m => generatedNinthLowerSpinTensorPackedCoordinate
          (generatedTenthAxisLowerRecoveryJointPackedStage04Words j) m)) n =
          2 * generatedNinthLowerSpinTensorPackedCoordinate
            (generatedTenthAxisLowerRecoveryJointPackedStage05Words j) n := by
  change ∀ n : Fin 4096,
    generatedNinthLowerSpinTensorFourierInteger (generatedNinthLowerSpinPackedHighBit 4)
      (generatedNinthLowerSpinTensorFourierInteger (generatedNinthLowerSpinPackedHighBit 5)
        (generatedNinthLowerSpinTensorPackedCoordinate
          (generatedTenthAxisLowerRecoveryJointPackedStage04Words j))) n =
      2 * generatedNinthLowerSpinTensorPackedCoordinate
        (generatedTenthAxisLowerRecoveryJointPackedStage05Words j) n
  apply generatedNinth_lower_spin_packed_high_pair_of_coordinates
    (generatedTenthAxisLowerRecoveryJointPackedStage04Words j)
    (generatedTenthAxisLowerRecoveryJointPackedStage05Words j) 4 5 (by decide)
  intro a i
  exact generatedTenth_axis_lower_recovery_joint_packed_pair04_signed_coordinates j a i

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
