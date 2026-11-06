/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthShortPacketQ
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthQCache00
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthQCache01

/-! Verified coordinate-image tables reduce complete actual short transports
to finite certificates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

/-- A checked coordinate table and complete finite preferred-Q packet images
transport the entire actual fifth short component. -/
theorem generatedAxisGlobalFifthShortFastPacket_transport (k : Fin 14)
    (hk : ∀ i, generatedAxisGlobalFifthChainQImage k 7 (qCoordinateGenerator i) =
      generatedAxisGlobalFifthQCache k i)
    (s : GeneratedAxisGlobalFifthShortPacketIndex → GriessShortIndex)
    (p : GeneratedAxisGlobalFifthShortPacketIndex → ZMod 2)
    (hc : ∀ i, generatedAxisGlobalFifthQFast k (generatedAxisGlobalFifthShortPacketQ i) =
      qCentral (p i) * griessShortQ (s i)) :
    localShortOperator (generatedAxisGlobalFifthShortWordFiber k)
        ((griessConwayEncode generatedFifthAxis).2.1) =
      ∑ i, (generatedAxisGlobalFifthShortPacketCoefficient i * qSign (p i)) •
        Pi.single (s i) (1 : ℝ) := by
  apply generatedAxisGlobalFifthShortPacket_transport
  intro i
  rw [generatedAxisGlobalFifthQFast_actual k hk, ← generatedAxisGlobalFifthShortPacketQ_actual]
  exact hc i

/-- The first genuine root word uses its unconditionally checked full coordinate table. -/
theorem generatedAxisGlobalFifthShortFastPacket_root00
    (s : GeneratedAxisGlobalFifthShortPacketIndex → GriessShortIndex)
    (p : GeneratedAxisGlobalFifthShortPacketIndex → ZMod 2)
    (hc : ∀ i, generatedAxisGlobalFifthQFast 0 (generatedAxisGlobalFifthShortPacketQ i) =
      qCentral (p i) * griessShortQ (s i)) :
    localShortOperator (generatedAxisGlobalFifthShortWordFiber 0)
        ((griessConwayEncode generatedFifthAxis).2.1) =
      ∑ i, (generatedAxisGlobalFifthShortPacketCoefficient i * qSign (p i)) •
        Pi.single (s i) (1 : ℝ) :=
  generatedAxisGlobalFifthShortFastPacket_transport 0 generatedAxisGlobalFifthQCache00_actual s p hc

/-- The second genuine root word uses its unconditionally checked full coordinate table. -/
theorem generatedAxisGlobalFifthShortFastPacket_root01
    (s : GeneratedAxisGlobalFifthShortPacketIndex → GriessShortIndex)
    (p : GeneratedAxisGlobalFifthShortPacketIndex → ZMod 2)
    (hc : ∀ i, generatedAxisGlobalFifthQFast 1 (generatedAxisGlobalFifthShortPacketQ i) =
      qCentral (p i) * griessShortQ (s i)) :
    localShortOperator (generatedAxisGlobalFifthShortWordFiber 1)
        ((griessConwayEncode generatedFifthAxis).2.1) =
      ∑ i, (generatedAxisGlobalFifthShortPacketCoefficient i * qSign (p i)) •
        Pi.single (s i) (1 : ℝ) :=
  generatedAxisGlobalFifthShortFastPacket_transport 1 generatedAxisGlobalFifthQCache01_actual s p hc

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
