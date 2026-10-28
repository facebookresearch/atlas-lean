/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingZeroRootOrbitTable

/-! Complete ordinary-kernel root transport certificate for one bounded packet of 216 roots. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 24000000

private def edgeSubIndex (k : Fin 12) (j : Fin 18) : Fin 216 :=
  ⟨18 * k.val + j.val, by omega⟩

private theorem edgeSubIndex_cover (j : Fin 216) :
    ∃ k : Fin 12, ∃ q : Fin 18, edgeSubIndex k q = j := by
  let k : Fin 12 := ⟨j.val / 18, by omega⟩
  let q : Fin 18 := ⟨j.val % 18, Nat.mod_lt _ (by decide)⟩
  exact ⟨k, q, Fin.ext (by dsimp [edgeSubIndex, k, q]; omega)⟩

private theorem inversePart00 : ∀ q : Fin 18,
    generatedFeasibleContainingZeroRootInverse
      (generatedFeasibleContainingZeroCachedAddress
        (generatedFeasibleContainingZeroRootNode (generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 0 q)))) =
      generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 0 q) := by decide +kernel

private theorem inversePart01 : ∀ q : Fin 18,
    generatedFeasibleContainingZeroRootInverse
      (generatedFeasibleContainingZeroCachedAddress
        (generatedFeasibleContainingZeroRootNode (generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 1 q)))) =
      generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 1 q) := by decide +kernel

private theorem inversePart02 : ∀ q : Fin 18,
    generatedFeasibleContainingZeroRootInverse
      (generatedFeasibleContainingZeroCachedAddress
        (generatedFeasibleContainingZeroRootNode (generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 2 q)))) =
      generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 2 q) := by decide +kernel

private theorem inversePart03 : ∀ q : Fin 18,
    generatedFeasibleContainingZeroRootInverse
      (generatedFeasibleContainingZeroCachedAddress
        (generatedFeasibleContainingZeroRootNode (generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 3 q)))) =
      generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 3 q) := by decide +kernel

private theorem inversePart04 : ∀ q : Fin 18,
    generatedFeasibleContainingZeroRootInverse
      (generatedFeasibleContainingZeroCachedAddress
        (generatedFeasibleContainingZeroRootNode (generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 4 q)))) =
      generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 4 q) := by decide +kernel

private theorem inversePart05 : ∀ q : Fin 18,
    generatedFeasibleContainingZeroRootInverse
      (generatedFeasibleContainingZeroCachedAddress
        (generatedFeasibleContainingZeroRootNode (generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 5 q)))) =
      generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 5 q) := by decide +kernel

private theorem inversePart06 : ∀ q : Fin 18,
    generatedFeasibleContainingZeroRootInverse
      (generatedFeasibleContainingZeroCachedAddress
        (generatedFeasibleContainingZeroRootNode (generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 6 q)))) =
      generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 6 q) := by decide +kernel

private theorem inversePart07 : ∀ q : Fin 18,
    generatedFeasibleContainingZeroRootInverse
      (generatedFeasibleContainingZeroCachedAddress
        (generatedFeasibleContainingZeroRootNode (generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 7 q)))) =
      generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 7 q) := by decide +kernel

private theorem inversePart08 : ∀ q : Fin 18,
    generatedFeasibleContainingZeroRootInverse
      (generatedFeasibleContainingZeroCachedAddress
        (generatedFeasibleContainingZeroRootNode (generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 8 q)))) =
      generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 8 q) := by decide +kernel

private theorem inversePart09 : ∀ q : Fin 18,
    generatedFeasibleContainingZeroRootInverse
      (generatedFeasibleContainingZeroCachedAddress
        (generatedFeasibleContainingZeroRootNode (generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 9 q)))) =
      generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 9 q) := by decide +kernel

private theorem inversePart10 : ∀ q : Fin 18,
    generatedFeasibleContainingZeroRootInverse
      (generatedFeasibleContainingZeroCachedAddress
        (generatedFeasibleContainingZeroRootNode (generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 10 q)))) =
      generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 10 q) := by decide +kernel

private theorem inversePart11 : ∀ q : Fin 18,
    generatedFeasibleContainingZeroRootInverse
      (generatedFeasibleContainingZeroCachedAddress
        (generatedFeasibleContainingZeroRootNode (generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 11 q)))) =
      generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 11 q) := by decide +kernel

/-- Every actual node address in this packet has its exact inverse address. -/
theorem generatedFeasibleContainingZeroRootPacket05_inverse : ∀ j : Fin 216,
    generatedFeasibleContainingZeroRootInverse
      (generatedFeasibleContainingZeroCachedAddress
        (generatedFeasibleContainingZeroRootNode (generatedFeasibleContainingZeroRootPacketIndex 5 j))) =
      generatedFeasibleContainingZeroRootPacketIndex 5 j := by
  intro j
  obtain ⟨k, q, hj⟩ := edgeSubIndex_cover j
  rw [← hj]
  fin_cases k
  · exact inversePart00 q
  · exact inversePart01 q
  · exact inversePart02 q
  · exact inversePart03 q
  · exact inversePart04 q
  · exact inversePart05 q
  · exact inversePart06 q
  · exact inversePart07 q
  · exact inversePart08 q
  · exact inversePart09 q
  · exact inversePart10 q
  · exact inversePart11 q

private theorem parent_ltPart00 : ∀ q : Fin 18,
    generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 0 q) ≠ 0 →
      (generatedFeasibleContainingZeroRootParent (generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 0 q))).val <
        (generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 0 q)).val := by decide +kernel

private theorem parent_ltPart01 : ∀ q : Fin 18,
    generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 1 q) ≠ 0 →
      (generatedFeasibleContainingZeroRootParent (generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 1 q))).val <
        (generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 1 q)).val := by decide +kernel

private theorem parent_ltPart02 : ∀ q : Fin 18,
    generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 2 q) ≠ 0 →
      (generatedFeasibleContainingZeroRootParent (generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 2 q))).val <
        (generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 2 q)).val := by decide +kernel

private theorem parent_ltPart03 : ∀ q : Fin 18,
    generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 3 q) ≠ 0 →
      (generatedFeasibleContainingZeroRootParent (generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 3 q))).val <
        (generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 3 q)).val := by decide +kernel

private theorem parent_ltPart04 : ∀ q : Fin 18,
    generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 4 q) ≠ 0 →
      (generatedFeasibleContainingZeroRootParent (generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 4 q))).val <
        (generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 4 q)).val := by decide +kernel

private theorem parent_ltPart05 : ∀ q : Fin 18,
    generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 5 q) ≠ 0 →
      (generatedFeasibleContainingZeroRootParent (generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 5 q))).val <
        (generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 5 q)).val := by decide +kernel

private theorem parent_ltPart06 : ∀ q : Fin 18,
    generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 6 q) ≠ 0 →
      (generatedFeasibleContainingZeroRootParent (generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 6 q))).val <
        (generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 6 q)).val := by decide +kernel

private theorem parent_ltPart07 : ∀ q : Fin 18,
    generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 7 q) ≠ 0 →
      (generatedFeasibleContainingZeroRootParent (generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 7 q))).val <
        (generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 7 q)).val := by decide +kernel

private theorem parent_ltPart08 : ∀ q : Fin 18,
    generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 8 q) ≠ 0 →
      (generatedFeasibleContainingZeroRootParent (generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 8 q))).val <
        (generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 8 q)).val := by decide +kernel

private theorem parent_ltPart09 : ∀ q : Fin 18,
    generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 9 q) ≠ 0 →
      (generatedFeasibleContainingZeroRootParent (generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 9 q))).val <
        (generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 9 q)).val := by decide +kernel

private theorem parent_ltPart10 : ∀ q : Fin 18,
    generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 10 q) ≠ 0 →
      (generatedFeasibleContainingZeroRootParent (generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 10 q))).val <
        (generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 10 q)).val := by decide +kernel

private theorem parent_ltPart11 : ∀ q : Fin 18,
    generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 11 q) ≠ 0 →
      (generatedFeasibleContainingZeroRootParent (generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 11 q))).val <
        (generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 11 q)).val := by decide +kernel

/-- Every noninitial actual root in this packet has a strictly earlier parent. -/
theorem generatedFeasibleContainingZeroRootPacket05_parent_lt : ∀ j : Fin 216,
    generatedFeasibleContainingZeroRootPacketIndex 5 j ≠ 0 →
      (generatedFeasibleContainingZeroRootParent (generatedFeasibleContainingZeroRootPacketIndex 5 j)).val <
        (generatedFeasibleContainingZeroRootPacketIndex 5 j).val := by
  intro j hn
  obtain ⟨k, q, hj⟩ := edgeSubIndex_cover j
  rw [← hj] at hn ⊢
  fin_cases k
  · exact parent_ltPart00 q hn
  · exact parent_ltPart01 q hn
  · exact parent_ltPart02 q hn
  · exact parent_ltPart03 q hn
  · exact parent_ltPart04 q hn
  · exact parent_ltPart05 q hn
  · exact parent_ltPart06 q hn
  · exact parent_ltPart07 q hn
  · exact parent_ltPart08 q hn
  · exact parent_ltPart09 q hn
  · exact parent_ltPart10 q hn
  · exact parent_ltPart11 q hn

private theorem signPart00 : ∀ q : Fin 18,
    generatedFeasibleContainingZeroRootSign (generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 0 q)) = 1 ∨
      generatedFeasibleContainingZeroRootSign (generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 0 q)) = -1 := by decide +kernel

private theorem signPart01 : ∀ q : Fin 18,
    generatedFeasibleContainingZeroRootSign (generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 1 q)) = 1 ∨
      generatedFeasibleContainingZeroRootSign (generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 1 q)) = -1 := by decide +kernel

private theorem signPart02 : ∀ q : Fin 18,
    generatedFeasibleContainingZeroRootSign (generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 2 q)) = 1 ∨
      generatedFeasibleContainingZeroRootSign (generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 2 q)) = -1 := by decide +kernel

private theorem signPart03 : ∀ q : Fin 18,
    generatedFeasibleContainingZeroRootSign (generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 3 q)) = 1 ∨
      generatedFeasibleContainingZeroRootSign (generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 3 q)) = -1 := by decide +kernel

private theorem signPart04 : ∀ q : Fin 18,
    generatedFeasibleContainingZeroRootSign (generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 4 q)) = 1 ∨
      generatedFeasibleContainingZeroRootSign (generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 4 q)) = -1 := by decide +kernel

private theorem signPart05 : ∀ q : Fin 18,
    generatedFeasibleContainingZeroRootSign (generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 5 q)) = 1 ∨
      generatedFeasibleContainingZeroRootSign (generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 5 q)) = -1 := by decide +kernel

private theorem signPart06 : ∀ q : Fin 18,
    generatedFeasibleContainingZeroRootSign (generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 6 q)) = 1 ∨
      generatedFeasibleContainingZeroRootSign (generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 6 q)) = -1 := by decide +kernel

private theorem signPart07 : ∀ q : Fin 18,
    generatedFeasibleContainingZeroRootSign (generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 7 q)) = 1 ∨
      generatedFeasibleContainingZeroRootSign (generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 7 q)) = -1 := by decide +kernel

private theorem signPart08 : ∀ q : Fin 18,
    generatedFeasibleContainingZeroRootSign (generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 8 q)) = 1 ∨
      generatedFeasibleContainingZeroRootSign (generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 8 q)) = -1 := by decide +kernel

private theorem signPart09 : ∀ q : Fin 18,
    generatedFeasibleContainingZeroRootSign (generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 9 q)) = 1 ∨
      generatedFeasibleContainingZeroRootSign (generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 9 q)) = -1 := by decide +kernel

private theorem signPart10 : ∀ q : Fin 18,
    generatedFeasibleContainingZeroRootSign (generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 10 q)) = 1 ∨
      generatedFeasibleContainingZeroRootSign (generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 10 q)) = -1 := by decide +kernel

private theorem signPart11 : ∀ q : Fin 18,
    generatedFeasibleContainingZeroRootSign (generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 11 q)) = 1 ∨
      generatedFeasibleContainingZeroRootSign (generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 11 q)) = -1 := by decide +kernel

/-- Every actual root edge in this packet has one of the two exact integral orientations. -/
theorem generatedFeasibleContainingZeroRootPacket05_sign : ∀ j : Fin 216,
    generatedFeasibleContainingZeroRootSign (generatedFeasibleContainingZeroRootPacketIndex 5 j) = 1 ∨
      generatedFeasibleContainingZeroRootSign (generatedFeasibleContainingZeroRootPacketIndex 5 j) = -1 := by
  intro j
  obtain ⟨k, q, hj⟩ := edgeSubIndex_cover j
  rw [← hj]
  fin_cases k
  · exact signPart00 q
  · exact signPart01 q
  · exact signPart02 q
  · exact signPart03 q
  · exact signPart04 q
  · exact signPart05 q
  · exact signPart06 q
  · exact signPart07 q
  · exact signPart08 q
  · exact signPart09 q
  · exact signPart10 q
  · exact signPart11 q

private theorem edgePart00 : ∀ q : Fin 18,
    generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 0 q) ≠ 0 → ∀ i : Fin 24,
      generatedFeasibleContainingZeroRootNumerator
        (generatedFeasibleContainingZeroRootLetter (generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 0 q)))
        (generatedFeasibleContainingZeroCachedIntegral
          (generatedFeasibleContainingZeroRootNode
            (generatedFeasibleContainingZeroRootParent (generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 0 q))))) i =
      2 * generatedFeasibleContainingZeroRootSign (generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 0 q)) *
        generatedFeasibleContainingZeroCachedIntegral
          (generatedFeasibleContainingZeroRootNode (generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 0 q))) i := by decide +kernel

private theorem edgePart01 : ∀ q : Fin 18,
    generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 1 q) ≠ 0 → ∀ i : Fin 24,
      generatedFeasibleContainingZeroRootNumerator
        (generatedFeasibleContainingZeroRootLetter (generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 1 q)))
        (generatedFeasibleContainingZeroCachedIntegral
          (generatedFeasibleContainingZeroRootNode
            (generatedFeasibleContainingZeroRootParent (generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 1 q))))) i =
      2 * generatedFeasibleContainingZeroRootSign (generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 1 q)) *
        generatedFeasibleContainingZeroCachedIntegral
          (generatedFeasibleContainingZeroRootNode (generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 1 q))) i := by decide +kernel

private theorem edgePart02 : ∀ q : Fin 18,
    generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 2 q) ≠ 0 → ∀ i : Fin 24,
      generatedFeasibleContainingZeroRootNumerator
        (generatedFeasibleContainingZeroRootLetter (generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 2 q)))
        (generatedFeasibleContainingZeroCachedIntegral
          (generatedFeasibleContainingZeroRootNode
            (generatedFeasibleContainingZeroRootParent (generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 2 q))))) i =
      2 * generatedFeasibleContainingZeroRootSign (generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 2 q)) *
        generatedFeasibleContainingZeroCachedIntegral
          (generatedFeasibleContainingZeroRootNode (generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 2 q))) i := by decide +kernel

private theorem edgePart03 : ∀ q : Fin 18,
    generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 3 q) ≠ 0 → ∀ i : Fin 24,
      generatedFeasibleContainingZeroRootNumerator
        (generatedFeasibleContainingZeroRootLetter (generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 3 q)))
        (generatedFeasibleContainingZeroCachedIntegral
          (generatedFeasibleContainingZeroRootNode
            (generatedFeasibleContainingZeroRootParent (generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 3 q))))) i =
      2 * generatedFeasibleContainingZeroRootSign (generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 3 q)) *
        generatedFeasibleContainingZeroCachedIntegral
          (generatedFeasibleContainingZeroRootNode (generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 3 q))) i := by decide +kernel

private theorem edgePart04 : ∀ q : Fin 18,
    generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 4 q) ≠ 0 → ∀ i : Fin 24,
      generatedFeasibleContainingZeroRootNumerator
        (generatedFeasibleContainingZeroRootLetter (generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 4 q)))
        (generatedFeasibleContainingZeroCachedIntegral
          (generatedFeasibleContainingZeroRootNode
            (generatedFeasibleContainingZeroRootParent (generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 4 q))))) i =
      2 * generatedFeasibleContainingZeroRootSign (generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 4 q)) *
        generatedFeasibleContainingZeroCachedIntegral
          (generatedFeasibleContainingZeroRootNode (generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 4 q))) i := by decide +kernel

private theorem edgePart05 : ∀ q : Fin 18,
    generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 5 q) ≠ 0 → ∀ i : Fin 24,
      generatedFeasibleContainingZeroRootNumerator
        (generatedFeasibleContainingZeroRootLetter (generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 5 q)))
        (generatedFeasibleContainingZeroCachedIntegral
          (generatedFeasibleContainingZeroRootNode
            (generatedFeasibleContainingZeroRootParent (generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 5 q))))) i =
      2 * generatedFeasibleContainingZeroRootSign (generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 5 q)) *
        generatedFeasibleContainingZeroCachedIntegral
          (generatedFeasibleContainingZeroRootNode (generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 5 q))) i := by decide +kernel

private theorem edgePart06 : ∀ q : Fin 18,
    generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 6 q) ≠ 0 → ∀ i : Fin 24,
      generatedFeasibleContainingZeroRootNumerator
        (generatedFeasibleContainingZeroRootLetter (generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 6 q)))
        (generatedFeasibleContainingZeroCachedIntegral
          (generatedFeasibleContainingZeroRootNode
            (generatedFeasibleContainingZeroRootParent (generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 6 q))))) i =
      2 * generatedFeasibleContainingZeroRootSign (generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 6 q)) *
        generatedFeasibleContainingZeroCachedIntegral
          (generatedFeasibleContainingZeroRootNode (generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 6 q))) i := by decide +kernel

private theorem edgePart07 : ∀ q : Fin 18,
    generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 7 q) ≠ 0 → ∀ i : Fin 24,
      generatedFeasibleContainingZeroRootNumerator
        (generatedFeasibleContainingZeroRootLetter (generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 7 q)))
        (generatedFeasibleContainingZeroCachedIntegral
          (generatedFeasibleContainingZeroRootNode
            (generatedFeasibleContainingZeroRootParent (generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 7 q))))) i =
      2 * generatedFeasibleContainingZeroRootSign (generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 7 q)) *
        generatedFeasibleContainingZeroCachedIntegral
          (generatedFeasibleContainingZeroRootNode (generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 7 q))) i := by decide +kernel

private theorem edgePart08 : ∀ q : Fin 18,
    generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 8 q) ≠ 0 → ∀ i : Fin 24,
      generatedFeasibleContainingZeroRootNumerator
        (generatedFeasibleContainingZeroRootLetter (generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 8 q)))
        (generatedFeasibleContainingZeroCachedIntegral
          (generatedFeasibleContainingZeroRootNode
            (generatedFeasibleContainingZeroRootParent (generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 8 q))))) i =
      2 * generatedFeasibleContainingZeroRootSign (generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 8 q)) *
        generatedFeasibleContainingZeroCachedIntegral
          (generatedFeasibleContainingZeroRootNode (generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 8 q))) i := by decide +kernel

private theorem edgePart09 : ∀ q : Fin 18,
    generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 9 q) ≠ 0 → ∀ i : Fin 24,
      generatedFeasibleContainingZeroRootNumerator
        (generatedFeasibleContainingZeroRootLetter (generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 9 q)))
        (generatedFeasibleContainingZeroCachedIntegral
          (generatedFeasibleContainingZeroRootNode
            (generatedFeasibleContainingZeroRootParent (generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 9 q))))) i =
      2 * generatedFeasibleContainingZeroRootSign (generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 9 q)) *
        generatedFeasibleContainingZeroCachedIntegral
          (generatedFeasibleContainingZeroRootNode (generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 9 q))) i := by decide +kernel

private theorem edgePart10 : ∀ q : Fin 18,
    generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 10 q) ≠ 0 → ∀ i : Fin 24,
      generatedFeasibleContainingZeroRootNumerator
        (generatedFeasibleContainingZeroRootLetter (generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 10 q)))
        (generatedFeasibleContainingZeroCachedIntegral
          (generatedFeasibleContainingZeroRootNode
            (generatedFeasibleContainingZeroRootParent (generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 10 q))))) i =
      2 * generatedFeasibleContainingZeroRootSign (generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 10 q)) *
        generatedFeasibleContainingZeroCachedIntegral
          (generatedFeasibleContainingZeroRootNode (generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 10 q))) i := by decide +kernel

private theorem edgePart11 : ∀ q : Fin 18,
    generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 11 q) ≠ 0 → ∀ i : Fin 24,
      generatedFeasibleContainingZeroRootNumerator
        (generatedFeasibleContainingZeroRootLetter (generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 11 q)))
        (generatedFeasibleContainingZeroCachedIntegral
          (generatedFeasibleContainingZeroRootNode
            (generatedFeasibleContainingZeroRootParent (generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 11 q))))) i =
      2 * generatedFeasibleContainingZeroRootSign (generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 11 q)) *
        generatedFeasibleContainingZeroCachedIntegral
          (generatedFeasibleContainingZeroRootNode (generatedFeasibleContainingZeroRootPacketIndex 5 (edgeSubIndex 11 q))) i := by decide +kernel

/-- All 24 physical coordinates of every genuine root edge in this packet are checked. -/
theorem generatedFeasibleContainingZeroRootPacket05_edge : ∀ j : Fin 216,
    generatedFeasibleContainingZeroRootPacketIndex 5 j ≠ 0 → ∀ i : Fin 24,
      generatedFeasibleContainingZeroRootNumerator
        (generatedFeasibleContainingZeroRootLetter (generatedFeasibleContainingZeroRootPacketIndex 5 j))
        (generatedFeasibleContainingZeroCachedIntegral
          (generatedFeasibleContainingZeroRootNode
            (generatedFeasibleContainingZeroRootParent (generatedFeasibleContainingZeroRootPacketIndex 5 j)))) i =
      2 * generatedFeasibleContainingZeroRootSign (generatedFeasibleContainingZeroRootPacketIndex 5 j) *
        generatedFeasibleContainingZeroCachedIntegral
          (generatedFeasibleContainingZeroRootNode (generatedFeasibleContainingZeroRootPacketIndex 5 j)) i  := by
  intro j hn i
  obtain ⟨k, q, hj⟩ := edgeSubIndex_cover j
  rw [← hj] at hn ⊢
  fin_cases k
  · exact edgePart00 q hn i
  · exact edgePart01 q hn i
  · exact edgePart02 q hn i
  · exact edgePart03 q hn i
  · exact edgePart04 q hn i
  · exact edgePart05 q hn i
  · exact edgePart06 q hn i
  · exact edgePart07 q hn i
  · exact edgePart08 q hn i
  · exact edgePart09 q hn i
  · exact edgePart10 q hn i
  · exact edgePart11 q hn i

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
