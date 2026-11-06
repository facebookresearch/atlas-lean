/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsPairQFinite
public import
FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthShortFastPacket

/-! Fully executable genuine preferred-Q inputs for all4136 fifth short-packet entries. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

/-- Every packet input evaluated through checked original physical-coordinate data. -/
def generatedAxisGlobalFifthPacketQFinite : GeneratedAxisGlobalFifthShortPacketIndex → Q
  | Sum.inl (s, p) => generatedAxisGlobalPairQFinite s p
  | Sum.inr p => generatedAxisGlobalFifthShortPacketQ (Sum.inr p)

/-- The finite packet input is exactly the entire genuine preferred lift. -/
theorem generatedAxisGlobalFifthPacketQFinite_actual
    (i : GeneratedAxisGlobalFifthShortPacketIndex) :
    generatedAxisGlobalFifthPacketQFinite i =
      griessShortQ (generatedAxisGlobalFifthShortPacketLabel i) := by
  rcases i with ⟨s, p⟩ | p
  · exact generatedAxisGlobalPairQFinite_actual s p
  · exact generatedAxisGlobalFifthShortPacketQ_actual (Sum.inr p)

/-- The executable inputs equal the already identified original packet preferred lifts. -/
theorem generatedAxisGlobalFifthPacketQFinite_eq
    (i : GeneratedAxisGlobalFifthShortPacketIndex) :
    generatedAxisGlobalFifthPacketQFinite i = generatedAxisGlobalFifthShortPacketQ i := by
  rw [generatedAxisGlobalFifthPacketQFinite_actual, generatedAxisGlobalFifthShortPacketQ_actual]

/-- Complete finite image certificates now determine the full actual real short transport. -/
theorem generatedAxisGlobalFifthPacketQFinite_transport (k : Fin 14)
    (hk : ∀ i, generatedAxisGlobalFifthChainQImage k 7 (qCoordinateGenerator i) =
      generatedAxisGlobalFifthQCache k i)
    (s : GeneratedAxisGlobalFifthShortPacketIndex → GriessShortIndex)
    (p : GeneratedAxisGlobalFifthShortPacketIndex → ZMod 2)
    (hc : ∀ i, generatedAxisGlobalFifthQFast k (generatedAxisGlobalFifthPacketQFinite i) =
      qCentral (p i) * griessShortQ (s i)) :
    localShortOperator (generatedAxisGlobalFifthShortWordFiber k)
        ((griessConwayEncode generatedFifthAxis).2.1) =
      ∑ i, (generatedAxisGlobalFifthShortPacketCoefficient i * qSign (p i)) •
        Pi.single (s i) (1 : ℝ) := by
  apply generatedAxisGlobalFifthShortFastPacket_transport k hk
  intro i
  rw [← generatedAxisGlobalFifthPacketQFinite_eq]
  exact hc i

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
