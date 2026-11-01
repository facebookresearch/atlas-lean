/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinPackedLowPairGeneric
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryPackedCandidate10Stage01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryPackedCandidate10Stage02

/-! Complete original candidate10 paired Fourier step1. All24columns and4096coordinates remain
  covered. -/
@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

/-- One complete source stage word, retaining the entire original prefix. -/
def generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Word (stage : ℕ) (j : Fin 24) (a : Fin
  256) : ℕ :=
  (if stage = 1 then generatedTenthAxisLowerRecoveryPackedCandidate10Stage01Words j else
    generatedTenthAxisLowerRecoveryPackedCandidate10Stage02Words j)
    ⟨a.val / 16, by omega⟩ ⟨a.val % 16, Nat.mod_lt _ (by decide)⟩

/-- Seven actual whole-word source terms retain all coordinate signs. -/
def generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Sources (j : Fin 24) (a : Fin 256) : Fin
  7 → ℕ :=
  generatedNinthLowerSpinPackedLowSources
    (generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Word 1 j a) 2 3

/-- All seven actual words, all target slots and the exact integral word equation. -/
def generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Condition (j : Fin 24) (a : Fin 256) :
  Prop :=
  (∀ z : Fin 7, generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Sources j a z < 512 ^ 16) ∧
  generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Word 2 j a < 512 ^ 16 ∧
  (∀ z : Fin 7, generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Sources j a z &&&
    generatedRootEightPackedGapEightMask = 0) ∧
  generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Word 2 j a &&&
    generatedRootEightPackedGapEightMask = 0 ∧
  (∑ z : Fin 7, generatedNinthLowerSpinPackedLowCoefficients z *
    generatedRootEightPackedSignedWord
      (generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Sources j a z)) =
      2 * generatedRootEightPackedSignedWord
        (generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Word 2 j a)

set_option maxHeartbeats 8000000 in
-- Check all original full words in one source column.
private theorem column_00 : ∀ a : Fin 256,
  generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Condition 0 a := by
  dsimp only [generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Condition,
    generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Sources,
    generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Word,
    generatedTenthAxisLowerRecoveryPackedCandidate10Stage01Words,
      generatedTenthAxisLowerRecoveryPackedCandidate10Stage02Words]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check all original full words in one source column.
private theorem column_01 : ∀ a : Fin 256,
  generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Condition 1 a := by
  dsimp only [generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Condition,
    generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Sources,
    generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Word,
    generatedTenthAxisLowerRecoveryPackedCandidate10Stage01Words,
      generatedTenthAxisLowerRecoveryPackedCandidate10Stage02Words]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check all original full words in one source column.
private theorem column_02 : ∀ a : Fin 256,
  generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Condition 2 a := by
  dsimp only [generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Condition,
    generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Sources,
    generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Word,
    generatedTenthAxisLowerRecoveryPackedCandidate10Stage01Words,
      generatedTenthAxisLowerRecoveryPackedCandidate10Stage02Words]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check all original full words in one source column.
private theorem column_03 : ∀ a : Fin 256,
  generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Condition 3 a := by
  dsimp only [generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Condition,
    generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Sources,
    generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Word,
    generatedTenthAxisLowerRecoveryPackedCandidate10Stage01Words,
      generatedTenthAxisLowerRecoveryPackedCandidate10Stage02Words]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check all original full words in one source column.
private theorem column_04 : ∀ a : Fin 256,
  generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Condition 4 a := by
  dsimp only [generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Condition,
    generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Sources,
    generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Word,
    generatedTenthAxisLowerRecoveryPackedCandidate10Stage01Words,
      generatedTenthAxisLowerRecoveryPackedCandidate10Stage02Words]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check all original full words in one source column.
private theorem column_05 : ∀ a : Fin 256,
  generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Condition 5 a := by
  dsimp only [generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Condition,
    generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Sources,
    generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Word,
    generatedTenthAxisLowerRecoveryPackedCandidate10Stage01Words,
      generatedTenthAxisLowerRecoveryPackedCandidate10Stage02Words]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check all original full words in one source column.
private theorem column_06 : ∀ a : Fin 256,
  generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Condition 6 a := by
  dsimp only [generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Condition,
    generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Sources,
    generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Word,
    generatedTenthAxisLowerRecoveryPackedCandidate10Stage01Words,
      generatedTenthAxisLowerRecoveryPackedCandidate10Stage02Words]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check all original full words in one source column.
private theorem column_07 : ∀ a : Fin 256,
  generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Condition 7 a := by
  dsimp only [generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Condition,
    generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Sources,
    generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Word,
    generatedTenthAxisLowerRecoveryPackedCandidate10Stage01Words,
      generatedTenthAxisLowerRecoveryPackedCandidate10Stage02Words]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check all original full words in one source column.
private theorem column_08 : ∀ a : Fin 256,
  generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Condition 8 a := by
  dsimp only [generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Condition,
    generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Sources,
    generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Word,
    generatedTenthAxisLowerRecoveryPackedCandidate10Stage01Words,
      generatedTenthAxisLowerRecoveryPackedCandidate10Stage02Words]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check all original full words in one source column.
private theorem column_09 : ∀ a : Fin 256,
  generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Condition 9 a := by
  dsimp only [generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Condition,
    generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Sources,
    generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Word,
    generatedTenthAxisLowerRecoveryPackedCandidate10Stage01Words,
      generatedTenthAxisLowerRecoveryPackedCandidate10Stage02Words]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check all original full words in one source column.
private theorem column_10 : ∀ a : Fin 256,
  generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Condition 10 a := by
  dsimp only [generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Condition,
    generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Sources,
    generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Word,
    generatedTenthAxisLowerRecoveryPackedCandidate10Stage01Words,
      generatedTenthAxisLowerRecoveryPackedCandidate10Stage02Words]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check all original full words in one source column.
private theorem column_11 : ∀ a : Fin 256,
  generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Condition 11 a := by
  dsimp only [generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Condition,
    generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Sources,
    generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Word,
    generatedTenthAxisLowerRecoveryPackedCandidate10Stage01Words,
      generatedTenthAxisLowerRecoveryPackedCandidate10Stage02Words]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check all original full words in one source column.
private theorem column_12 : ∀ a : Fin 256,
  generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Condition 12 a := by
  dsimp only [generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Condition,
    generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Sources,
    generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Word,
    generatedTenthAxisLowerRecoveryPackedCandidate10Stage01Words,
      generatedTenthAxisLowerRecoveryPackedCandidate10Stage02Words]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check all original full words in one source column.
private theorem column_13 : ∀ a : Fin 256,
  generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Condition 13 a := by
  dsimp only [generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Condition,
    generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Sources,
    generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Word,
    generatedTenthAxisLowerRecoveryPackedCandidate10Stage01Words,
      generatedTenthAxisLowerRecoveryPackedCandidate10Stage02Words]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check all original full words in one source column.
private theorem column_14 : ∀ a : Fin 256,
  generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Condition 14 a := by
  dsimp only [generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Condition,
    generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Sources,
    generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Word,
    generatedTenthAxisLowerRecoveryPackedCandidate10Stage01Words,
      generatedTenthAxisLowerRecoveryPackedCandidate10Stage02Words]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check all original full words in one source column.
private theorem column_15 : ∀ a : Fin 256,
  generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Condition 15 a := by
  dsimp only [generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Condition,
    generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Sources,
    generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Word,
    generatedTenthAxisLowerRecoveryPackedCandidate10Stage01Words,
      generatedTenthAxisLowerRecoveryPackedCandidate10Stage02Words]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check all original full words in one source column.
private theorem column_16 : ∀ a : Fin 256,
  generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Condition 16 a := by
  dsimp only [generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Condition,
    generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Sources,
    generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Word,
    generatedTenthAxisLowerRecoveryPackedCandidate10Stage01Words,
      generatedTenthAxisLowerRecoveryPackedCandidate10Stage02Words]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check all original full words in one source column.
private theorem column_17 : ∀ a : Fin 256,
  generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Condition 17 a := by
  dsimp only [generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Condition,
    generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Sources,
    generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Word,
    generatedTenthAxisLowerRecoveryPackedCandidate10Stage01Words,
      generatedTenthAxisLowerRecoveryPackedCandidate10Stage02Words]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check all original full words in one source column.
private theorem column_18 : ∀ a : Fin 256,
  generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Condition 18 a := by
  dsimp only [generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Condition,
    generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Sources,
    generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Word,
    generatedTenthAxisLowerRecoveryPackedCandidate10Stage01Words,
      generatedTenthAxisLowerRecoveryPackedCandidate10Stage02Words]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check all original full words in one source column.
private theorem column_19 : ∀ a : Fin 256,
  generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Condition 19 a := by
  dsimp only [generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Condition,
    generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Sources,
    generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Word,
    generatedTenthAxisLowerRecoveryPackedCandidate10Stage01Words,
      generatedTenthAxisLowerRecoveryPackedCandidate10Stage02Words]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check all original full words in one source column.
private theorem column_20 : ∀ a : Fin 256,
  generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Condition 20 a := by
  dsimp only [generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Condition,
    generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Sources,
    generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Word,
    generatedTenthAxisLowerRecoveryPackedCandidate10Stage01Words,
      generatedTenthAxisLowerRecoveryPackedCandidate10Stage02Words]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check all original full words in one source column.
private theorem column_21 : ∀ a : Fin 256,
  generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Condition 21 a := by
  dsimp only [generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Condition,
    generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Sources,
    generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Word,
    generatedTenthAxisLowerRecoveryPackedCandidate10Stage01Words,
      generatedTenthAxisLowerRecoveryPackedCandidate10Stage02Words]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check all original full words in one source column.
private theorem column_22 : ∀ a : Fin 256,
  generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Condition 22 a := by
  dsimp only [generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Condition,
    generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Sources,
    generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Word,
    generatedTenthAxisLowerRecoveryPackedCandidate10Stage01Words,
      generatedTenthAxisLowerRecoveryPackedCandidate10Stage02Words]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check all original full words in one source column.
private theorem column_23 : ∀ a : Fin 256,
  generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Condition 23 a := by
  dsimp only [generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Condition,
    generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Sources,
    generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Word,
    generatedTenthAxisLowerRecoveryPackedCandidate10Stage01Words,
      generatedTenthAxisLowerRecoveryPackedCandidate10Stage02Words]
  decide +kernel

/-- Every original complete prefix has all seven actual word certificates. -/
theorem generatedTenth_axis_lower_recovery_packed_candidate10_pair01_certificate : ∀ j : Fin 24, ∀
  a : Fin 256,
    generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Condition j a := by
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
theorem generatedTenth_axis_lower_recovery_packed_candidate10_pair01_signed_coordinates (j : Fin
  24) (a : Fin 256) :
    ∀ i : Fin 16, (∑ z : Fin 7, generatedNinthLowerSpinPackedLowCoefficients z *
      generatedRootEightPackedSignedDigit
        (generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Sources j a z) i) =
        2 * generatedRootEightPackedSignedDigit
          (generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Word 2 j a) i := by
  have h := generatedTenth_axis_lower_recovery_packed_candidate10_pair01_certificate j a
  apply generatedRootEight_packed_signed_bounded_terms (by decide)
    (generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Sources j a)
      (generatedTenthAxisLowerRecoveryPackedCandidate10Pair01Word 2 j a)
    generatedNinthLowerSpinPackedLowCoefficients
  · intro z
    fin_cases z <;> decide
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1
  · exact h.2.2.2.1
  · exact h.2.2.2.2

/-- The exact full actual Fourier statement covers all24columns and4096coordinates. -/
theorem generatedTenth_axis_lower_recovery_packed_candidate10_pair01_actual_fourier (j : Fin 24) :
  ∀ n : Fin 4096,
    generatedNinthLowerSpinTensorFourierInteger 2
      (generatedNinthLowerSpinTensorFourierInteger 3
        (fun m => generatedNinthLowerSpinTensorPackedCoordinate
          (generatedTenthAxisLowerRecoveryPackedCandidate10Stage01Words j) m)) n =
          2 * generatedNinthLowerSpinTensorPackedCoordinate
            (generatedTenthAxisLowerRecoveryPackedCandidate10Stage02Words j) n := by
  change ∀ n : Fin 4096,
    generatedNinthLowerSpinTensorFourierInteger ⟨(2 : Fin 4).val, by omega⟩
      (generatedNinthLowerSpinTensorFourierInteger ⟨(3 : Fin 4).val, by omega⟩
        (generatedNinthLowerSpinTensorPackedCoordinate
          (generatedTenthAxisLowerRecoveryPackedCandidate10Stage01Words j))) n =
      2 * generatedNinthLowerSpinTensorPackedCoordinate
        (generatedTenthAxisLowerRecoveryPackedCandidate10Stage02Words j) n
  apply generatedNinth_lower_spin_packed_low_pair_of_coordinates
    (generatedTenthAxisLowerRecoveryPackedCandidate10Stage01Words j)
    (generatedTenthAxisLowerRecoveryPackedCandidate10Stage02Words j) 2 3 (by decide)
  intro a i
  exact generatedTenth_axis_lower_recovery_packed_candidate10_pair01_signed_coordinates j a i

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
