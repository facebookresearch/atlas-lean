/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingZeroRootOrbitPacket00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingZeroRootOrbitPacket01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingZeroRootOrbitPacket02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingZeroRootOrbitPacket03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingZeroRootOrbitPacket04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingZeroRootOrbitPacket05
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingZeroRootOrbitPacket06
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingZeroRootOrbitPacket07
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingZeroRootOrbitPacket08
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingZeroRootOrbitPacket09

/-! Full actual root certificates assembled from all ten bounded packets without exclusions. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

private theorem packet_address (n : Fin 2160) :
    ∃ k : Fin 10, ∃ j : Fin 216, generatedFeasibleContainingZeroRootPacketIndex k j = n := by
  let k : Fin 10 := ⟨n.val / 216, by omega⟩
  let j : Fin 216 := ⟨n.val % 216, Nat.mod_lt _ (by decide)⟩
  exact ⟨k, j, Fin.ext (by dsimp [generatedFeasibleContainingZeroRootPacketIndex, k, j]; omega)⟩

/-- Every node has a verified inverse local address. -/
theorem generatedFeasibleContainingZeroRoot_inverse :
    ∀ n : Fin 2160,
      generatedFeasibleContainingZeroRootInverse
        (generatedFeasibleContainingZeroCachedAddress (generatedFeasibleContainingZeroRootNode n)) = n := by
  intro n
  obtain ⟨k, j, hj⟩ := packet_address n
  rw [← hj]
  fin_cases k
  · exact generatedFeasibleContainingZeroRootPacket00_inverse j
  · exact generatedFeasibleContainingZeroRootPacket01_inverse j
  · exact generatedFeasibleContainingZeroRootPacket02_inverse j
  · exact generatedFeasibleContainingZeroRootPacket03_inverse j
  · exact generatedFeasibleContainingZeroRootPacket04_inverse j
  · exact generatedFeasibleContainingZeroRootPacket05_inverse j
  · exact generatedFeasibleContainingZeroRootPacket06_inverse j
  · exact generatedFeasibleContainingZeroRootPacket07_inverse j
  · exact generatedFeasibleContainingZeroRootPacket08_inverse j
  · exact generatedFeasibleContainingZeroRootPacket09_inverse j

/-- The full actual node table has no duplicate preferred roots. -/
theorem generatedFeasibleContainingZeroRootNode_injective :
    Function.Injective generatedFeasibleContainingZeroRootNode := by
  intro n m h
  have hh := congrArg (fun r => generatedFeasibleContainingZeroRootInverse
    (generatedFeasibleContainingZeroCachedAddress r)) h
  simpa only [generatedFeasibleContainingZeroRoot_inverse] using hh

/-- Every parent is strictly earlier, so this is a complete finite proof tree. -/
theorem generatedFeasibleContainingZeroRootParent_lt :
    ∀ n : Fin 2160, n ≠ 0 → (generatedFeasibleContainingZeroRootParent n).val < n.val := by
  intro n hn
  obtain ⟨k, j, hj⟩ := packet_address n
  rw [← hj] at hn ⊢
  fin_cases k
  · exact generatedFeasibleContainingZeroRootPacket00_parent_lt j hn
  · exact generatedFeasibleContainingZeroRootPacket01_parent_lt j hn
  · exact generatedFeasibleContainingZeroRootPacket02_parent_lt j hn
  · exact generatedFeasibleContainingZeroRootPacket03_parent_lt j hn
  · exact generatedFeasibleContainingZeroRootPacket04_parent_lt j hn
  · exact generatedFeasibleContainingZeroRootPacket05_parent_lt j hn
  · exact generatedFeasibleContainingZeroRootPacket06_parent_lt j hn
  · exact generatedFeasibleContainingZeroRootPacket07_parent_lt j hn
  · exact generatedFeasibleContainingZeroRootPacket08_parent_lt j hn
  · exact generatedFeasibleContainingZeroRootPacket09_parent_lt j hn

/-- Every actual preferred-root edge has one of its two genuine integral orientations. -/
theorem generatedFeasibleContainingZeroRootSign_values :
    ∀ n : Fin 2160,
      generatedFeasibleContainingZeroRootSign n = 1 ∨
        generatedFeasibleContainingZeroRootSign n = -1 := by
  intro n
  obtain ⟨k, j, hj⟩ := packet_address n
  rw [← hj]
  fin_cases k
  · exact generatedFeasibleContainingZeroRootPacket00_sign j
  · exact generatedFeasibleContainingZeroRootPacket01_sign j
  · exact generatedFeasibleContainingZeroRootPacket02_sign j
  · exact generatedFeasibleContainingZeroRootPacket03_sign j
  · exact generatedFeasibleContainingZeroRootPacket04_sign j
  · exact generatedFeasibleContainingZeroRootPacket05_sign j
  · exact generatedFeasibleContainingZeroRootPacket06_sign j
  · exact generatedFeasibleContainingZeroRootPacket07_sign j
  · exact generatedFeasibleContainingZeroRootPacket08_sign j
  · exact generatedFeasibleContainingZeroRootPacket09_sign j

/-- Every coordinate of every tree edge agrees with the complete actual physical action. -/
theorem generatedFeasibleContainingZeroRoot_edge :
    ∀ n : Fin 2160, n ≠ 0 → ∀ i : Fin 24,
      generatedFeasibleContainingZeroRootNumerator (generatedFeasibleContainingZeroRootLetter n)
        (generatedFeasibleContainingZeroCachedIntegral
          (generatedFeasibleContainingZeroRootNode (generatedFeasibleContainingZeroRootParent n))) i =
      2 * generatedFeasibleContainingZeroRootSign n *
        generatedFeasibleContainingZeroCachedIntegral (generatedFeasibleContainingZeroRootNode n) i := by
  intro n hn i
  obtain ⟨k, j, hj⟩ := packet_address n
  rw [← hj] at hn ⊢
  fin_cases k
  · exact generatedFeasibleContainingZeroRootPacket00_edge j hn i
  · exact generatedFeasibleContainingZeroRootPacket01_edge j hn i
  · exact generatedFeasibleContainingZeroRootPacket02_edge j hn i
  · exact generatedFeasibleContainingZeroRootPacket03_edge j hn i
  · exact generatedFeasibleContainingZeroRootPacket04_edge j hn i
  · exact generatedFeasibleContainingZeroRootPacket05_edge j hn i
  · exact generatedFeasibleContainingZeroRootPacket06_edge j hn i
  · exact generatedFeasibleContainingZeroRootPacket07_edge j hn i
  · exact generatedFeasibleContainingZeroRootPacket08_edge j hn i
  · exact generatedFeasibleContainingZeroRootPacket09_edge j hn i

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
