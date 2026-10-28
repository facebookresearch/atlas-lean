/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthRoot08Packet
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthPhaseRoots

/-! The complete original fifth-axis root-8 triality destination.
This source-addressed name makes no claim about a descriptive orbit class. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
-- The literal seven-stage original word has a deep elaboration spine.
set_option maxRecDepth 10000

/-- The original phase-preserving local normalization at binary root 8. -/
def generatedFifthRootEightLocal : H := generatedAxisGlobalFifthShortLocalWord 8

/-- The literal original local word followed by the original triality generator. -/
def generatedFifthRootEightAxisWord : ↥G :=
  extraIntoGenerated * localIntoGenerated generatedFifthRootEightLocal * generatedFifthAxisWord

/-- This prototype is an actual word image of the original signed octad axis. -/
def generatedFifthRootEightAxis : GriessSpace :=
  generatedFifthRootEightAxisWord.val
    (conwayShortAxis (Sum.inr (Sum.inl (generatedFourthOctad, 0))) 0)

/-- The literal generated-group word agrees with the original local/triality action. -/
theorem generatedFifthRootEightAxis_local_expression :
    generatedFifthRootEightAxis = sExtra (rhoLocal generatedFifthRootEightLocal
      generatedFifthAxis) := by
  rfl

/-- The entire original Conway packet includes every matrix, short and tensor coordinate. -/
def generatedFifthRootEightPacket : ConwayRawSpace :=
  generatedAxisGlobalRawTrialityFormula generatedAxisGlobalFifthRoot08Packet

/-- No constituent or central phase is omitted from this actual prototype packet. -/
theorem generatedFifthRootEightPacket_actual :
    griessConwayEncode generatedFifthRootEightAxis = generatedFifthRootEightPacket := by
  exact generatedAxisGlobalFifthRoot08Packet_triality

/-- The actual prototype is in the global orbit of every original signed-short axis. -/
theorem generatedFifthRootEightAxis_mem_generatedOrbit (r : GriessShortIndex) (c : ZMod 2) :
    generatedFifthRootEightAxis ∈ generatedVectorOrbit (conwayShortAxis r c) := by
  obtain ⟨h, hh⟩ := generatedAxis_local_signed_transitive r
    (Sum.inr (Sum.inl (generatedFourthOctad, 0))) c 0
  refine ⟨generatedFifthRootEightAxisWord * localIntoGenerated h, ?_⟩
  change generatedFifthRootEightAxisWord.val (rhoLocal h (conwayShortAxis r c)) = _
  rw [hh]
  rfl

/-- The inverse-triality output at the identical root has the same full-axis local orbit. -/
theorem generatedFifthRootEightAxis_inverse_local_orbit :
    ∃ h : H, generatedFifthRootEightAxis =
      rhoLocal h (sExtra⁻¹ (rhoLocal generatedFifthRootEightLocal generatedFifthAxis)) := by
  exact generatedAxisGlobalFifthMergedRoot_orbit 4

/-- The actual original matrix coordinates are precisely the matrix of the complete packet. -/
theorem generatedFifthRootEight_matrix :
    (griessConwayEncode generatedFifthRootEightAxis).1 = generatedFifthRootEightPacket.1 := by
  rw [generatedFifthRootEightPacket_actual]

/-- The actual signed-short coordinates are precisely those of the complete packet. -/
theorem generatedFifthRootEight_short :
    (griessConwayEncode generatedFifthRootEightAxis).2.1 = generatedFifthRootEightPacket.2.1 := by
  rw [generatedFifthRootEightPacket_actual]

/-- All 98,304 original physical tensor coordinates retain the full source normalization. -/
theorem generatedFifthRootEight_tensor :
    (griessConwayEncode generatedFifthRootEightAxis).2.2 = generatedFifthRootEightPacket.2.2 := by
  rw [generatedFifthRootEightPacket_actual]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
