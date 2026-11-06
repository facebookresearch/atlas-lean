/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightIncomingCertifiedFiber
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightIncomingCentralOrbitTransport

/-! An actual compact incoming destination and its complete final triality local orbit. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

/-- The actual full incoming Griess vector under the genuine certified local element. -/
def generatedRootEightIncomingDestination : GriessSpace :=
  rhoLocal generatedRootEightIncomingCertifiedLocal generatedFifthAxis

/-- Genuine final triality applied to the actual complete compact incoming vector. -/
def generatedRootEightIncomingTrialityDestination : GriessSpace :=
  sExtra generatedRootEightIncomingDestination

/-- The complete pretriality matrix and signed-short components equal the original packet. -/
theorem generatedRootEight_incoming_destination_matrix_short :
    (griessConwayEncode generatedRootEightIncomingDestination).1 =
        generatedAxisGlobalFifthRoot08Packet.1 ∧
    (griessConwayEncode generatedRootEightIncomingDestination).2.1 =
        generatedAxisGlobalFifthRoot08Packet.2.1 := by
  have ht := generatedTwelfth_full_Q_matrix_short_blocks generatedRootEightIncomingCertifiedFiber
    (generatedTenthQWordFiber 8) generatedRootEight_incoming_compact_source_conjugation
    generatedFifthAxis
  rw [generatedTenth_Q_word_fiber_local, generatedAxisGlobalFifthRoot08Packet_actual] at ht
  exact ht

/-- An actual local element of trivial projection connects the final compact and original axes. -/
theorem generatedRootEight_incoming_destination_projection_orbit :
    ∃ u : H, projH u = 1 ∧ generatedFifthRootEightAxis =
      rhoLocal u generatedRootEightIncomingTrialityDestination := by
  exact generatedRootEight_incoming_central_projection_orbit
    generatedRootEightIncomingCertifiedFiber generatedRootEight_incoming_compact_source_conjugation

/-- Every attained full final compact-axis fixer transfers to the original actual axis. -/
theorem generatedRootEight_incoming_destination_fixer_transfer (h : H)
    (hfix : rhoLocal h generatedRootEightIncomingTrialityDestination =
      generatedRootEightIncomingTrialityDestination) :
    ∃ k : H, projH k = projH h ∧
      rhoLocal k generatedFifthRootEightAxis = generatedFifthRootEightAxis := by
  exact generatedRootEight_incoming_central_fixer_transfer generatedRootEightIncomingCertifiedFiber
    generatedRootEight_incoming_compact_source_conjugation h hfix

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
