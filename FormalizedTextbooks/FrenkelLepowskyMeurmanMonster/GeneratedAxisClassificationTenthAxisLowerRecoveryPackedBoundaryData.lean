/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinPackedHighPairGeneric
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryPackedBoundaryWord
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryTwoFixerTensorCircuitData

/-! Ungated complete boundary word interfaces for the two actual compact tensor operators. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The original input word at one complete eight-bit prefix. -/
def generatedTenthPackedBoundaryInputWord (j : Fin 24) (a : Fin 256) : ℕ :=
  generatedTenthAxisLowerRecoveryPackedInputWords j
    ⟨a.val / 16, by omega⟩ ⟨a.val % 16, Nat.mod_lt _ (by decide)⟩

/-- The original full cache word at one complete eight-bit prefix. -/
def generatedTenthPackedBoundaryStageWord (g : Fin 2) (s : ℕ) (j : Fin 24)
    (a : Fin 256) : ℕ :=
  (if g = 0 then generatedTenthAxisLowerRecoveryJointPackedCache
      ⟨s % 7, Nat.mod_lt _ (by decide)⟩ j
    else generatedTenthAxisLowerRecoveryPackedCandidate10Cache
      ⟨s % 6, Nat.mod_lt _ (by decide)⟩ j)
    ⟨a.val / 16, by omega⟩ ⟨a.val % 16, Nat.mod_lt _ (by decide)⟩

/-- Each source slot evaluates the genuine inverse right label and second quadratic phase. -/
def generatedTenthPackedBoundaryPreWord (g : Fin 2) (k : Fin 24) (a : Fin 256) : ℕ :=
  generatedTenthPackedBoundaryWord fun i =>
    generatedTenthTwoFixerTensorPreInteger g
      (fun m => generatedTenthTwoFixerTensorInput m k)
      (generatedNinthLowerSpinPackedPrefixIndex a i)

/-- Each source slot evaluates the genuine inverse left label and full Pauli/quadratic phase. -/
def generatedTenthPackedBoundaryPostWord (g : Fin 2) (j : Fin 24) (a : Fin 256) : ℕ :=
  generatedTenthPackedBoundaryWord fun i =>
    generatedTenthTwoFixerTensorPostInteger g
      (fun m => generatedTenthTwoFixerTensorState g (generatedTenthTwoFixerTensorPairs g).length
        m j) (generatedNinthLowerSpinPackedPrefixIndex a i)

/-- Complete computable small-word bounds; recorded discovery maxima do not prove this predicate. -/
def GeneratedTenthPackedBoundaryBounds : Prop :=
  (∀ (j : Fin 24) (a : Fin 256),
    generatedTenthPackedBoundaryAbsMax (generatedTenthPackedBoundaryInputWord j a) ≤ 176) ∧
  (∀ (g : Fin 2) (j : Fin 24) (a : Fin 256),
    generatedTenthPackedBoundaryAbsMax (generatedTenthPackedBoundaryStageWord g 0 j a) ≤ 144) ∧
  (∀ (g : Fin 2) (j : Fin 24) (a : Fin 256),
    generatedTenthPackedBoundaryAbsMax (generatedTenthPackedBoundaryStageWord g
      (generatedTenthTwoFixerTensorPairs g).length j a) ≤ 176)

/-- All256 original output word prefixes and all24 physical columns retain the true denominator. -/
def GeneratedTenthPackedBoundaryStartWords : Prop :=
  ∀ (g : Fin 2) (j : Fin 24) (a : Fin 256),
    (∑ k : Fin 24, generatedTenthTwoFixerTensorNumerator g j k *
      generatedRootEightPackedSignedWord (generatedTenthPackedBoundaryPreWord g k a)) =
        (generatedTenthTwoFixerTensorDenominator g : ℤ) *
          generatedRootEightPackedSignedWord (generatedTenthPackedBoundaryStageWord g 0 j a)

/-- Complete genuine post words and complete final original cache words must match the input. -/
def GeneratedTenthPackedBoundaryFinishWords : Prop :=
  ∀ (g : Fin 2) (j : Fin 24) (a : Fin 256),
    generatedRootEightPackedSignedWord (generatedTenthPackedBoundaryPostWord g j a) =
      generatedRootEightPackedSignedWord (generatedTenthPackedBoundaryInputWord j a) ∧
    generatedTenthPackedBoundaryStageWord g ((generatedTenthTwoFixerTensorPairs g).length + 1)
      j a = generatedTenthPackedBoundaryInputWord j a

set_option maxHeartbeats 1000000 in
-- Only48 actual physical numerator row weights and the two literal denominators are evaluated.
/-- The small budget concerns the original physical numerator, without an orientation change. -/
theorem generatedTenth_packed_boundary_row_budget : ∀ (g : Fin 2) (j : Fin 24),
    (generatedTenthTwoFixerTensorDenominator g : ℤ) = 4 ∧
      (∑ k : Fin 24, |generatedTenthTwoFixerTensorNumerator g j k|) ≤ 16 := by
  decide +kernel

/-- Original input decoding preserves every original slot. -/
theorem generatedTenth_packed_boundary_input_digit (j : Fin 24) (a : Fin 256) (i : Fin 16) :
    generatedRootEightPackedSignedDigit (generatedTenthPackedBoundaryInputWord j a) i =
      generatedTenthTwoFixerTensorInput (generatedNinthLowerSpinPackedPrefixIndex a i) j := by
  exact (generatedNinth_lower_spin_packed_prefix_coordinate
    (generatedTenthAxisLowerRecoveryPackedInputWords j) a i).symm

/-- Original stage decoding preserves every original slot and the exact original stage index. -/
theorem generatedTenth_packed_boundary_stage_digit (g : Fin 2) (s : ℕ) (j : Fin 24)
    (a : Fin 256) (i : Fin 16) :
    generatedRootEightPackedSignedDigit (generatedTenthPackedBoundaryStageWord g s j a) i =
      generatedTenthTwoFixerTensorState g s (generatedNinthLowerSpinPackedPrefixIndex a i) j := by
  exact (generatedNinth_lower_spin_packed_prefix_coordinate
    (if g = 0 then generatedTenthAxisLowerRecoveryJointPackedCache
        ⟨s % 7, Nat.mod_lt _ (by decide)⟩ j
      else generatedTenthAxisLowerRecoveryPackedCandidate10Cache
        ⟨s % 6, Nat.mod_lt _ (by decide)⟩ j) a i).symm

/-- Both output prefix and slot recover the entire original twelve-bit label. -/
theorem generatedTenth_packed_boundary_prefix_recover (n : Fin 4096) :
    generatedNinthLowerSpinPackedPrefixIndex ⟨n.val / 16, by omega⟩
      ⟨n.val % 16, Nat.mod_lt _ (by decide)⟩ = n := by
  apply Fin.ext
  dsimp [generatedNinthLowerSpinPackedPrefixIndex]
  omega

/-- Existing complete original input width and gap certificates are reused directly. -/
theorem generatedTenth_packed_boundary_input_width_gap (j : Fin 24) (a : Fin 256) :
    generatedTenthPackedBoundaryInputWord j a < 512 ^ 16 ∧
      generatedTenthPackedBoundaryInputWord j a &&& generatedRootEightPackedGapEightMask = 0 :=
  gPackedInput_word_bounds_gap j _ _

/-- Existing original stage-zero certificates keep all source gap and width information. -/
theorem generatedTenth_packed_boundary_zero_width_gap (g : Fin 2) (j : Fin 24) (a : Fin 256) :
    generatedTenthPackedBoundaryStageWord g 0 j a < 512 ^ 16 ∧
      generatedTenthPackedBoundaryStageWord g 0 j a &&&
        generatedRootEightPackedGapEightMask = 0 := by
  fin_cases g
  · simpa [generatedTenthPackedBoundaryStageWord,
      generatedTenthAxisLowerRecoveryJointPackedCache] using
      generatedTenth_joint_packed_stage00_word_bounds_gap j
        ⟨a.val / 16, by omega⟩ ⟨a.val % 16, Nat.mod_lt _ (by decide)⟩
  · simpa [generatedTenthPackedBoundaryStageWord,
      generatedTenthAxisLowerRecoveryPackedCandidate10Cache] using
      gPackedCandidate10Stage00_word_bounds_gap j
        ⟨a.val / 16, by omega⟩ ⟨a.val % 16, Nat.mod_lt _ (by decide)⟩

/-- Both actual final pair stages retain their full original width and gap certificates. -/
theorem generatedTenth_packed_boundary_last_width_gap (g : Fin 2) (j : Fin 24) (a : Fin 256) :
    generatedTenthPackedBoundaryStageWord g (generatedTenthTwoFixerTensorPairs g).length j a <
      512 ^ 16 ∧
    generatedTenthPackedBoundaryStageWord g (generatedTenthTwoFixerTensorPairs g).length j a &&&
      generatedRootEightPackedGapEightMask = 0 := by
  fin_cases g
  · simpa [generatedTenthPackedBoundaryStageWord, generatedTenthTwoFixerTensorPairs,
      generatedTenthAxisLowerRecoveryJointPackedCache] using
      generatedTenth_joint_packed_stage05_word_bounds_gap j
        ⟨a.val / 16, by omega⟩ ⟨a.val % 16, Nat.mod_lt _ (by decide)⟩
  · simpa [generatedTenthPackedBoundaryStageWord, generatedTenthTwoFixerTensorPairs,
      generatedTenthAxisLowerRecoveryPackedCandidate10Cache] using
      gPackedCandidate10Stage04_word_bounds_gap j
        ⟨a.val / 16, by omega⟩ ⟨a.val % 16, Nat.mod_lt _ (by decide)⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
