/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinPackedLowPairGeneric

/-! All original source prefixes and all signed slots for generator10 low pair4. -/
@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

/-- One original complete sixteen-slot source word. -/
def generatedNinthLowerSpinPackedLowPair10Pair04Word (stage : ℕ) (j : Fin 24) (a : Fin 256) : ℕ :=
  generatedNinthLowerSpinTensorStageWords 10 stage j
    ⟨a.val / 16, by omega⟩ ⟨a.val % 16, Nat.mod_lt _ (by decide)⟩

/-- Seven actual whole-word source terms retain all coordinate signs. -/
def generatedNinthLowerSpinPackedLowPair10Pair04Sources (j : Fin 24) (a : Fin 256) : Fin 7 → ℕ :=
  generatedNinthLowerSpinPackedLowSources (generatedNinthLowerSpinPackedLowPair10Pair04Word 4 j a) 0 1

/-- All seven actual words, all target slots and the exact integral word equation. -/
def generatedNinthLowerSpinPackedLowPair10Pair04Condition (j : Fin 24) (a : Fin 256) : Prop :=
  (∀ z : Fin 7, generatedNinthLowerSpinPackedLowPair10Pair04Sources j a z < 512 ^ 16) ∧
  generatedNinthLowerSpinPackedLowPair10Pair04Word 5 j a < 512 ^ 16 ∧
  (∀ z : Fin 7, generatedNinthLowerSpinPackedLowPair10Pair04Sources j a z &&& generatedRootEightPackedGapEightMask = 0) ∧
  generatedNinthLowerSpinPackedLowPair10Pair04Word 5 j a &&& generatedRootEightPackedGapEightMask = 0 ∧
  (∑ z : Fin 7, generatedNinthLowerSpinPackedLowCoefficients z *
    generatedRootEightPackedSignedWord (generatedNinthLowerSpinPackedLowPair10Pair04Sources j a z)) =
      2 * generatedRootEightPackedSignedWord (generatedNinthLowerSpinPackedLowPair10Pair04Word 5 j a)

set_option maxHeartbeats 8000000 in
-- Check all original full words in one source column.
private theorem column_00 : ∀ a : Fin 256, generatedNinthLowerSpinPackedLowPair10Pair04Condition 0 a := by
  dsimp only [generatedNinthLowerSpinPackedLowPair10Pair04Condition, generatedNinthLowerSpinPackedLowPair10Pair04Sources, generatedNinthLowerSpinPackedLowPair10Pair04Word,
    generatedNinthLowerSpinTensorStageWords, generatedNinthLowerSpinTensorStageWords10]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check all original full words in one source column.
private theorem column_01 : ∀ a : Fin 256, generatedNinthLowerSpinPackedLowPair10Pair04Condition 1 a := by
  dsimp only [generatedNinthLowerSpinPackedLowPair10Pair04Condition, generatedNinthLowerSpinPackedLowPair10Pair04Sources, generatedNinthLowerSpinPackedLowPair10Pair04Word,
    generatedNinthLowerSpinTensorStageWords, generatedNinthLowerSpinTensorStageWords10]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check all original full words in one source column.
private theorem column_02 : ∀ a : Fin 256, generatedNinthLowerSpinPackedLowPair10Pair04Condition 2 a := by
  dsimp only [generatedNinthLowerSpinPackedLowPair10Pair04Condition, generatedNinthLowerSpinPackedLowPair10Pair04Sources, generatedNinthLowerSpinPackedLowPair10Pair04Word,
    generatedNinthLowerSpinTensorStageWords, generatedNinthLowerSpinTensorStageWords10]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check all original full words in one source column.
private theorem column_03 : ∀ a : Fin 256, generatedNinthLowerSpinPackedLowPair10Pair04Condition 3 a := by
  dsimp only [generatedNinthLowerSpinPackedLowPair10Pair04Condition, generatedNinthLowerSpinPackedLowPair10Pair04Sources, generatedNinthLowerSpinPackedLowPair10Pair04Word,
    generatedNinthLowerSpinTensorStageWords, generatedNinthLowerSpinTensorStageWords10]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check all original full words in one source column.
private theorem column_04 : ∀ a : Fin 256, generatedNinthLowerSpinPackedLowPair10Pair04Condition 4 a := by
  dsimp only [generatedNinthLowerSpinPackedLowPair10Pair04Condition, generatedNinthLowerSpinPackedLowPair10Pair04Sources, generatedNinthLowerSpinPackedLowPair10Pair04Word,
    generatedNinthLowerSpinTensorStageWords, generatedNinthLowerSpinTensorStageWords10]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check all original full words in one source column.
private theorem column_05 : ∀ a : Fin 256, generatedNinthLowerSpinPackedLowPair10Pair04Condition 5 a := by
  dsimp only [generatedNinthLowerSpinPackedLowPair10Pair04Condition, generatedNinthLowerSpinPackedLowPair10Pair04Sources, generatedNinthLowerSpinPackedLowPair10Pair04Word,
    generatedNinthLowerSpinTensorStageWords, generatedNinthLowerSpinTensorStageWords10]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check all original full words in one source column.
private theorem column_06 : ∀ a : Fin 256, generatedNinthLowerSpinPackedLowPair10Pair04Condition 6 a := by
  dsimp only [generatedNinthLowerSpinPackedLowPair10Pair04Condition, generatedNinthLowerSpinPackedLowPair10Pair04Sources, generatedNinthLowerSpinPackedLowPair10Pair04Word,
    generatedNinthLowerSpinTensorStageWords, generatedNinthLowerSpinTensorStageWords10]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check all original full words in one source column.
private theorem column_07 : ∀ a : Fin 256, generatedNinthLowerSpinPackedLowPair10Pair04Condition 7 a := by
  dsimp only [generatedNinthLowerSpinPackedLowPair10Pair04Condition, generatedNinthLowerSpinPackedLowPair10Pair04Sources, generatedNinthLowerSpinPackedLowPair10Pair04Word,
    generatedNinthLowerSpinTensorStageWords, generatedNinthLowerSpinTensorStageWords10]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check all original full words in one source column.
private theorem column_08 : ∀ a : Fin 256, generatedNinthLowerSpinPackedLowPair10Pair04Condition 8 a := by
  dsimp only [generatedNinthLowerSpinPackedLowPair10Pair04Condition, generatedNinthLowerSpinPackedLowPair10Pair04Sources, generatedNinthLowerSpinPackedLowPair10Pair04Word,
    generatedNinthLowerSpinTensorStageWords, generatedNinthLowerSpinTensorStageWords10]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check all original full words in one source column.
private theorem column_09 : ∀ a : Fin 256, generatedNinthLowerSpinPackedLowPair10Pair04Condition 9 a := by
  dsimp only [generatedNinthLowerSpinPackedLowPair10Pair04Condition, generatedNinthLowerSpinPackedLowPair10Pair04Sources, generatedNinthLowerSpinPackedLowPair10Pair04Word,
    generatedNinthLowerSpinTensorStageWords, generatedNinthLowerSpinTensorStageWords10]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check all original full words in one source column.
private theorem column_10 : ∀ a : Fin 256, generatedNinthLowerSpinPackedLowPair10Pair04Condition 10 a := by
  dsimp only [generatedNinthLowerSpinPackedLowPair10Pair04Condition, generatedNinthLowerSpinPackedLowPair10Pair04Sources, generatedNinthLowerSpinPackedLowPair10Pair04Word,
    generatedNinthLowerSpinTensorStageWords, generatedNinthLowerSpinTensorStageWords10]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check all original full words in one source column.
private theorem column_11 : ∀ a : Fin 256, generatedNinthLowerSpinPackedLowPair10Pair04Condition 11 a := by
  dsimp only [generatedNinthLowerSpinPackedLowPair10Pair04Condition, generatedNinthLowerSpinPackedLowPair10Pair04Sources, generatedNinthLowerSpinPackedLowPair10Pair04Word,
    generatedNinthLowerSpinTensorStageWords, generatedNinthLowerSpinTensorStageWords10]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check all original full words in one source column.
private theorem column_12 : ∀ a : Fin 256, generatedNinthLowerSpinPackedLowPair10Pair04Condition 12 a := by
  dsimp only [generatedNinthLowerSpinPackedLowPair10Pair04Condition, generatedNinthLowerSpinPackedLowPair10Pair04Sources, generatedNinthLowerSpinPackedLowPair10Pair04Word,
    generatedNinthLowerSpinTensorStageWords, generatedNinthLowerSpinTensorStageWords10]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check all original full words in one source column.
private theorem column_13 : ∀ a : Fin 256, generatedNinthLowerSpinPackedLowPair10Pair04Condition 13 a := by
  dsimp only [generatedNinthLowerSpinPackedLowPair10Pair04Condition, generatedNinthLowerSpinPackedLowPair10Pair04Sources, generatedNinthLowerSpinPackedLowPair10Pair04Word,
    generatedNinthLowerSpinTensorStageWords, generatedNinthLowerSpinTensorStageWords10]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check all original full words in one source column.
private theorem column_14 : ∀ a : Fin 256, generatedNinthLowerSpinPackedLowPair10Pair04Condition 14 a := by
  dsimp only [generatedNinthLowerSpinPackedLowPair10Pair04Condition, generatedNinthLowerSpinPackedLowPair10Pair04Sources, generatedNinthLowerSpinPackedLowPair10Pair04Word,
    generatedNinthLowerSpinTensorStageWords, generatedNinthLowerSpinTensorStageWords10]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check all original full words in one source column.
private theorem column_15 : ∀ a : Fin 256, generatedNinthLowerSpinPackedLowPair10Pair04Condition 15 a := by
  dsimp only [generatedNinthLowerSpinPackedLowPair10Pair04Condition, generatedNinthLowerSpinPackedLowPair10Pair04Sources, generatedNinthLowerSpinPackedLowPair10Pair04Word,
    generatedNinthLowerSpinTensorStageWords, generatedNinthLowerSpinTensorStageWords10]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check all original full words in one source column.
private theorem column_16 : ∀ a : Fin 256, generatedNinthLowerSpinPackedLowPair10Pair04Condition 16 a := by
  dsimp only [generatedNinthLowerSpinPackedLowPair10Pair04Condition, generatedNinthLowerSpinPackedLowPair10Pair04Sources, generatedNinthLowerSpinPackedLowPair10Pair04Word,
    generatedNinthLowerSpinTensorStageWords, generatedNinthLowerSpinTensorStageWords10]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check all original full words in one source column.
private theorem column_17 : ∀ a : Fin 256, generatedNinthLowerSpinPackedLowPair10Pair04Condition 17 a := by
  dsimp only [generatedNinthLowerSpinPackedLowPair10Pair04Condition, generatedNinthLowerSpinPackedLowPair10Pair04Sources, generatedNinthLowerSpinPackedLowPair10Pair04Word,
    generatedNinthLowerSpinTensorStageWords, generatedNinthLowerSpinTensorStageWords10]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check all original full words in one source column.
private theorem column_18 : ∀ a : Fin 256, generatedNinthLowerSpinPackedLowPair10Pair04Condition 18 a := by
  dsimp only [generatedNinthLowerSpinPackedLowPair10Pair04Condition, generatedNinthLowerSpinPackedLowPair10Pair04Sources, generatedNinthLowerSpinPackedLowPair10Pair04Word,
    generatedNinthLowerSpinTensorStageWords, generatedNinthLowerSpinTensorStageWords10]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check all original full words in one source column.
private theorem column_19 : ∀ a : Fin 256, generatedNinthLowerSpinPackedLowPair10Pair04Condition 19 a := by
  dsimp only [generatedNinthLowerSpinPackedLowPair10Pair04Condition, generatedNinthLowerSpinPackedLowPair10Pair04Sources, generatedNinthLowerSpinPackedLowPair10Pair04Word,
    generatedNinthLowerSpinTensorStageWords, generatedNinthLowerSpinTensorStageWords10]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check all original full words in one source column.
private theorem column_20 : ∀ a : Fin 256, generatedNinthLowerSpinPackedLowPair10Pair04Condition 20 a := by
  dsimp only [generatedNinthLowerSpinPackedLowPair10Pair04Condition, generatedNinthLowerSpinPackedLowPair10Pair04Sources, generatedNinthLowerSpinPackedLowPair10Pair04Word,
    generatedNinthLowerSpinTensorStageWords, generatedNinthLowerSpinTensorStageWords10]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check all original full words in one source column.
private theorem column_21 : ∀ a : Fin 256, generatedNinthLowerSpinPackedLowPair10Pair04Condition 21 a := by
  dsimp only [generatedNinthLowerSpinPackedLowPair10Pair04Condition, generatedNinthLowerSpinPackedLowPair10Pair04Sources, generatedNinthLowerSpinPackedLowPair10Pair04Word,
    generatedNinthLowerSpinTensorStageWords, generatedNinthLowerSpinTensorStageWords10]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check all original full words in one source column.
private theorem column_22 : ∀ a : Fin 256, generatedNinthLowerSpinPackedLowPair10Pair04Condition 22 a := by
  dsimp only [generatedNinthLowerSpinPackedLowPair10Pair04Condition, generatedNinthLowerSpinPackedLowPair10Pair04Sources, generatedNinthLowerSpinPackedLowPair10Pair04Word,
    generatedNinthLowerSpinTensorStageWords, generatedNinthLowerSpinTensorStageWords10]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check all original full words in one source column.
private theorem column_23 : ∀ a : Fin 256, generatedNinthLowerSpinPackedLowPair10Pair04Condition 23 a := by
  dsimp only [generatedNinthLowerSpinPackedLowPair10Pair04Condition, generatedNinthLowerSpinPackedLowPair10Pair04Sources, generatedNinthLowerSpinPackedLowPair10Pair04Word,
    generatedNinthLowerSpinTensorStageWords, generatedNinthLowerSpinTensorStageWords10]
  decide +kernel

/-- Every original complete prefix has all seven actual word certificates. -/
theorem generatedNinth_lower_spin_packed_low_pair10_pair04_certificate : ∀ j : Fin 24, ∀ a : Fin 256,
    generatedNinthLowerSpinPackedLowPair10Pair04Condition j a := by
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

/-- Every original signed coordinate follows from the exact seven-word certificate. -/
theorem generatedNinth_lower_spin_packed_low_pair10_pair04_signed_coordinates (j : Fin 24) (a : Fin 256) :
    ∀ i : Fin 16, (∑ z : Fin 7, generatedNinthLowerSpinPackedLowCoefficients z *
      generatedRootEightPackedSignedDigit (generatedNinthLowerSpinPackedLowPair10Pair04Sources j a z) i) =
        2 * generatedRootEightPackedSignedDigit (generatedNinthLowerSpinPackedLowPair10Pair04Word 5 j a) i := by
  have h := generatedNinth_lower_spin_packed_low_pair10_pair04_certificate j a
  apply generatedRootEight_packed_signed_bounded_terms (by decide)
    (generatedNinthLowerSpinPackedLowPair10Pair04Sources j a) (generatedNinthLowerSpinPackedLowPair10Pair04Word 5 j a)
    generatedNinthLowerSpinPackedLowCoefficients
  · intro z
    fin_cases z <;> decide
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1
  · exact h.2.2.2.1
  · exact h.2.2.2.2

/-- The exact full actual Fourier statement covers all24columns and4096coordinates. -/
theorem generatedNinth_lower_spin_packed_low_pair10_pair04_actual_fourier (j : Fin 24) : ∀ n : Fin 4096,
    generatedNinthLowerSpinTensorFourierInteger 0
      (generatedNinthLowerSpinTensorFourierInteger 1
        (fun m => generatedNinthLowerSpinTensorStageInteger 10 4 m j)) n =
          2 * generatedNinthLowerSpinTensorStageInteger 10 5 n j := by
  change ∀ n : Fin 4096,
    generatedNinthLowerSpinTensorFourierInteger ⟨(0 : Fin 4).val, by omega⟩
      (generatedNinthLowerSpinTensorFourierInteger ⟨(1 : Fin 4).val, by omega⟩
        (generatedNinthLowerSpinTensorPackedCoordinate
          (generatedNinthLowerSpinTensorStageWords 10 4 j))) n =
      2 * generatedNinthLowerSpinTensorPackedCoordinate
        (generatedNinthLowerSpinTensorStageWords 10 5 j) n
  apply generatedNinth_lower_spin_packed_low_pair_of_coordinates
    (generatedNinthLowerSpinTensorStageWords 10 4 j)
    (generatedNinthLowerSpinTensorStageWords 10 5 j) 0 1 (by decide)
  intro a i
  exact generatedNinth_lower_spin_packed_low_pair10_pair04_signed_coordinates j a i

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
