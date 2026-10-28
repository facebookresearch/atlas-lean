/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryPackedBoundaryWord
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoverySourceColumnSpinSumGeneric
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinPackedHighPairGeneric

/-! Ungated complete incoming B packing. Original signed source values and zeros are retained. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- One fixed physical column multiplies sixteen complete original spin-sum source labels. -/
def generatedTenthIncomingBPackedSourceWord (cache : Fin 8 → Fin 4096 → ℤ)
    (r : Fin 8) (a : Fin 256) : ℕ :=
  generatedTenthPackedBoundaryWord fun s =>
    cache r (generatedNinthLowerSpinPackedPrefixIndex a s)

/-- Every B lookup, including zero, keeps its original spin label and physical index. -/
def generatedTenthIncomingBPackedTargetWord (B : Fin 4096 → Fin 24 → ℤ)
    (j : Fin 24) (a : Fin 256) : ℕ :=
  generatedTenthPackedBoundaryWord fun s =>
    B (generatedNinthLowerSpinPackedPrefixIndex a s) j

/-- The maximum concerns original B integers before residue encoding can hide a large value. -/
def generatedTenthIncomingBPackedTargetAbsMax (B : Fin 4096 → Fin 24 → ℤ)
    (j : Fin 24) (a : Fin 256) : ℕ :=
  Finset.univ.sup fun s : Fin 16 =>
    (B (generatedNinthLowerSpinPackedPrefixIndex a s) j).natAbs

/-- All6144 target word blocks certify all98304 original B magnitudes, without aliasing residues. -/
def GeneratedTenthIncomingBPackedTargetBound (B : Fin 4096 → Fin 24 → ℤ) : Prop :=
  ∀ (j : Fin 24) (a : Fin 256), generatedTenthIncomingBPackedTargetAbsMax B j a ≤ 12

/-- Complete24times256 signed equations preserve the physical source column and scalar4. -/
def GeneratedTenthIncomingBPackedWordCertificate (cache : Fin 8 → Fin 4096 → ℤ)
    (B : Fin 4096 → Fin 24 → ℤ) : Prop :=
  ∀ (j : Fin 24) (a : Fin 256),
    (∑ r : Fin 8, generatedTenthSourceSpatialWordLiteralNumerator j
      (generatedTwelfthTensorSourceCoordinate r) *
        generatedRootEightPackedSignedWord (generatedTenthIncomingBPackedSourceWord cache r a)) =
      4 * generatedRootEightPackedSignedWord (generatedTenthIncomingBPackedTargetWord B j a)

set_option maxHeartbeats 1000000 in
-- Only192 entries in the eight original physical source columns are evaluated here.
/-- The actual physical source numerator has magnitude at most2 in every required source column. -/
theorem generatedTenth_incoming_B_packed_physical_bound : ∀ (j : Fin 24) (r : Fin 8),
    |generatedTenthSourceSpatialWordLiteralNumerator j
      (generatedTwelfthTensorSourceCoordinate r)| ≤ 2 := by
  decide +kernel

/-- The complete target block bound applies to each original source integer, before packing. -/
theorem generatedTenth_incoming_B_packed_target_abs
    (B : Fin 4096 → Fin 24 → ℤ) (hb : GeneratedTenthIncomingBPackedTargetBound B)
    (j : Fin 24) (a : Fin 256) (s : Fin 16) :
    |B (generatedNinthLowerSpinPackedPrefixIndex a s) j| ≤ 12 := by
  have hi : (B (generatedNinthLowerSpinPackedPrefixIndex a s) j).natAbs ≤ 12 :=
    (Finset.le_sup (Finset.mem_univ s)).trans (hb j a)
  have hc : ((B (generatedNinthLowerSpinPackedPrefixIndex a s) j).natAbs : ℤ) ≤ 12 := by
    exact_mod_cast hi
  simpa only [Int.natCast_natAbs] using hc

/-- All sixteen source word slots are the original genuine spin-sum cache integers. -/
theorem generatedTenth_incoming_B_packed_source_digit
    (cache : Fin 8 → Fin 4096 → ℤ)
    (hc : GeneratedTenthSourceColumnSpinSumCacheCertificate cache)
    (r : Fin 8) (a : Fin 256) (s : Fin 16) :
    generatedRootEightPackedSignedDigit (generatedTenthIncomingBPackedSourceWord cache r a) s =
      cache r (generatedNinthLowerSpinPackedPrefixIndex a s) := by
  apply generatedTenth_packed_boundary_word_digit
  intro i
  have hi := (hc r (generatedNinthLowerSpinPackedPrefixIndex a i)).2.2
  linarith

/-- All sixteen target word slots retain their original complete signed B source value. -/
theorem generatedTenth_incoming_B_packed_target_digit
    (B : Fin 4096 → Fin 24 → ℤ) (hb : GeneratedTenthIncomingBPackedTargetBound B)
    (j : Fin 24) (a : Fin 256) (s : Fin 16) :
    generatedRootEightPackedSignedDigit (generatedTenthIncomingBPackedTargetWord B j a) s =
      B (generatedNinthLowerSpinPackedPrefixIndex a s) j := by
  apply generatedTenth_packed_boundary_word_digit
  intro i
  have hi := generatedTenth_incoming_B_packed_target_abs B hb j a i
  linarith

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
