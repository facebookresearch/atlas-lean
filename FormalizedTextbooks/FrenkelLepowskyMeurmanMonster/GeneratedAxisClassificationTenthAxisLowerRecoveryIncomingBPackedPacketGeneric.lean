/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryIncomingBPackedActual

/-! Ungated complete incoming B finite packets; no declaration has passed Lean. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Every packet retains sixty-four consecutive original complete word prefixes. -/
def generatedTenthIncomingBPackedPacketPrefix (b : Fin 4) (u : Fin 64) : Fin 256 :=
  ⟨64 * b.val + u.val, by omega⟩

/-- Every packet checks all sixteen original B integers of each of its sixty-four prefixes. -/
def GeneratedTenthIncomingBPackedBoundPacketCondition (j : Fin 24) (b : Fin 4) : Prop :=
  ∀ u : Fin 64, generatedTenthIncomingBPackedTargetAbsMax generatedTenthIncomingTensorPackedCache
    j (generatedTenthIncomingBPackedPacketPrefix b u) ≤ 12

/-- Every complete signed source word keeps all eight physical columns and the scalar 4. -/
def GeneratedTenthIncomingBPackedWordPacketCondition (j : Fin 24) (b : Fin 4) : Prop :=
  ∀ u : Fin 64,
    (∑ r : Fin 8, generatedTenthSourceSpatialWordLiteralNumerator j
      (generatedTwelfthTensorSourceCoordinate r) * generatedRootEightPackedSignedWord
        (generatedTenthIncomingBPackedSourceWord generatedTenthSourceColumnSpinSumCache r
          (generatedTenthIncomingBPackedPacketPrefix b u))) =
      4 * generatedRootEightPackedSignedWord
        (generatedTenthIncomingBPackedTargetWord generatedTenthIncomingTensorPackedCache j
          (generatedTenthIncomingBPackedPacketPrefix b u))

/-- All original prefixes are covered, including every zero lookup and signed slot. -/
theorem generatedTenth_incoming_B_packed_bound_of_packets
    (h : ∀ j b, GeneratedTenthIncomingBPackedBoundPacketCondition j b) :
    GeneratedTenthIncomingBPackedActualBound := by
  intro j a
  let b : Fin 4 := ⟨a.val / 64, by omega⟩
  let u : Fin 64 := ⟨a.val % 64, Nat.mod_lt _ (by decide)⟩
  have he : generatedTenthIncomingBPackedPacketPrefix b u = a := by
    apply Fin.ext
    dsimp [generatedTenthIncomingBPackedPacketPrefix, b, u]
    omega
  have hh := h j b u
  simpa only [he] using hh

/-- All original signed whole-word equations follow from the complete packet cover. -/
theorem generatedTenth_incoming_B_packed_words_of_packets
    (h : ∀ j b, GeneratedTenthIncomingBPackedWordPacketCondition j b) :
    GeneratedTenthIncomingBPackedActualWords := by
  intro j a
  let b : Fin 4 := ⟨a.val / 64, by omega⟩
  let u : Fin 64 := ⟨a.val % 64, Nat.mod_lt _ (by decide)⟩
  have he : generatedTenthIncomingBPackedPacketPrefix b u = a := by
    apply Fin.ext
    dsimp [generatedTenthIncomingBPackedPacketPrefix, b, u]
    omega
  have hh := h j b u
  simpa only [he] using hh

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
