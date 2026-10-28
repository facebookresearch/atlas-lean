/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthRoot00Packet
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthRoot01Packet
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthRoot02Packet
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthRoot03Packet
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthRoot04Packet
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthRoot05Packet
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthRoot06Packet
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthRoot07Packet
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthRoot08Packet
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthRoot09Packet
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthRoot10Packet
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthRoot11
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthRoot12Packet
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthRoot13Packet

/-! Complete original real packets for all fourteen actual fifth-axis transition roots. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Complete original matrix, signed short, and physical tensor packets in root order. -/
def generatedAxisGlobalFifthAllPackets : Fin 14 → ConwayRawSpace :=
  ![generatedAxisGlobalFifthRoot00Packet,
    generatedAxisGlobalFifthRoot01Packet,
    generatedAxisGlobalFifthRoot02Packet,
    generatedAxisGlobalFifthRoot03Packet,
    generatedAxisGlobalFifthRoot04Packet,
    generatedAxisGlobalFifthRoot05Packet,
    generatedAxisGlobalFifthRoot06Packet,
    generatedAxisGlobalFifthRoot07Packet,
    generatedAxisGlobalFifthRoot08Packet,
    generatedAxisGlobalFifthRoot09Packet,
    generatedAxisGlobalFifthRoot10Packet,
    generatedAxisGlobalFifthRawPacket,
    generatedAxisGlobalFifthRoot12Packet,
    generatedAxisGlobalFifthRoot13Packet]

set_option maxHeartbeats 1000000 in
-- Dispatch fourteen complete actual-coordinate proofs without expanding their tensor sums.
/-- Every displayed packet is the full original actual local-word image of the fifth axis. -/
theorem generatedAxisGlobalFifthAllPackets_actual (k : Fin 14) :
    griessConwayEncode
      (rhoLocal (generatedAxisGlobalFifthShortLocalWord k) generatedFifthAxis) =
        generatedAxisGlobalFifthAllPackets k := by
  fin_cases k
  · exact generatedAxisGlobalFifthRoot00Packet_actual
  · exact generatedAxisGlobalFifthRoot01Packet_actual
  · exact generatedAxisGlobalFifthRoot02Packet_actual
  · exact generatedAxisGlobalFifthRoot03Packet_actual
  · exact generatedAxisGlobalFifthRoot04Packet_actual
  · exact generatedAxisGlobalFifthRoot05Packet_actual
  · exact generatedAxisGlobalFifthRoot06Packet_actual
  · exact generatedAxisGlobalFifthRoot07Packet_actual
  · exact generatedAxisGlobalFifthRoot08Packet_actual
  · exact generatedAxisGlobalFifthRoot09Packet_actual
  · exact generatedAxisGlobalFifthRoot10Packet_actual
  · change griessConwayEncode
        (rhoLocal (generatedAxisGlobalFifthShortLocalWord 11) generatedFifthAxis) =
          generatedAxisGlobalFifthRawPacket
    rw [generatedAxisGlobalFifthRoot11_packet]
    exact generatedAxisGlobalFifthRawPacket_eq
  · exact generatedAxisGlobalFifthRoot12Packet_actual
  · exact generatedAxisGlobalFifthRoot13Packet_actual

/-- All fourteen original positive-triality outputs are fixed by the complete actual packets. -/
theorem generatedAxisGlobalFifthAllPackets_triality (k : Fin 14) :
    griessConwayEncode
      (sExtra (rhoLocal (generatedAxisGlobalFifthShortLocalWord k) generatedFifthAxis)) =
        generatedAxisGlobalRawTrialityFormula (generatedAxisGlobalFifthAllPackets k) := by
  rw [generatedAxisGlobalRawTrialityFormula_actual, generatedAxisGlobalFifthAllPackets_actual]

/-- All fourteen inverse-triality outputs retain every original constituent and central phase. -/
theorem generatedAxisGlobalFifthAllPackets_inverse (k : Fin 14) :
    griessConwayEncode
      (sExtra.symm (rhoLocal (generatedAxisGlobalFifthShortLocalWord k) generatedFifthAxis)) =
        generatedAxisGlobalRawInverseFormula (generatedAxisGlobalFifthAllPackets k) := by
  rw [generatedAxisGlobalRawInverseFormula_actual, generatedAxisGlobalFifthAllPackets_actual]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
