/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthRoot03Packet
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthPhaseRoots

/-! A genuine further fifth-axis transition. The ordinal names select literal
words; identifying a descriptive source class and counting its stabilizer are
separate mathematical tasks. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
-- The literal seven-stage original word has a deep elaboration spine.
set_option maxRecDepth 10000

/-- The original phase-preserving local normalization at binary root 3. -/
def generatedEleventhLocal : H := generatedAxisGlobalFifthShortLocalWord 3

/-- The literal original local word followed by the original triality generator. -/
def generatedEleventhAxisWord : ↥G :=
  extraIntoGenerated * localIntoGenerated generatedEleventhLocal * generatedFifthAxisWord

/-- This prototype is an actual word image of the original signed octad axis. -/
def generatedEleventhAxis : GriessSpace :=
  generatedEleventhAxisWord.val
    (conwayShortAxis (Sum.inr (Sum.inl (generatedFourthOctad, 0))) 0)

/-- The literal generated-group word agrees with the original local/triality action. -/
theorem generatedEleventhAxis_local_expression :
    generatedEleventhAxis = sExtra (rhoLocal generatedEleventhLocal generatedFifthAxis) := by
  rfl

/-- The entire original Conway packet includes every matrix, short and tensor coordinate. -/
def generatedEleventhPacket : ConwayRawSpace :=
  generatedAxisGlobalRawTrialityFormula generatedAxisGlobalFifthRoot03Packet

/-- No constituent or central phase is omitted from this actual prototype packet. -/
theorem generatedEleventhPacket_actual :
    griessConwayEncode generatedEleventhAxis = generatedEleventhPacket := by
  exact generatedAxisGlobalFifthRoot03Packet_triality

/-- The actual prototype is in the global orbit of every original signed-short axis. -/
theorem generatedEleventhAxis_mem_generatedOrbit (r : GriessShortIndex) (c : ZMod 2) :
    generatedEleventhAxis ∈ generatedVectorOrbit (conwayShortAxis r c) := by
  obtain ⟨h, hh⟩ := generatedAxis_local_signed_transitive r
    (Sum.inr (Sum.inl (generatedFourthOctad, 0))) c 0
  refine ⟨generatedEleventhAxisWord * localIntoGenerated h, ?_⟩
  change generatedEleventhAxisWord.val (rhoLocal h (conwayShortAxis r c)) = _
  rw [hh]
  rfl

/-- The inverse-triality output at the identical root has the same full-axis local orbit. -/
theorem generatedEleventhAxis_inverse_local_orbit :
    ∃ h : H, generatedEleventhAxis =
      rhoLocal h (sExtra⁻¹ (rhoLocal generatedEleventhLocal generatedFifthAxis)) := by
  exact generatedAxisGlobalFifthMergedRoot_orbit 1

/-- The actual original matrix coordinates are precisely the matrix of the complete packet. -/
theorem generatedEleventh_matrix :
    (griessConwayEncode generatedEleventhAxis).1 = generatedEleventhPacket.1 := by
  rw [generatedEleventhPacket_actual]

/-- The actual signed-short coordinates are precisely those of the complete packet. -/
theorem generatedEleventh_short :
    (griessConwayEncode generatedEleventhAxis).2.1 = generatedEleventhPacket.2.1 := by
  rw [generatedEleventhPacket_actual]

/-- All 98,304 original physical tensor coordinates retain the full source normalization. -/
theorem generatedEleventh_tensor :
    (griessConwayEncode generatedEleventhAxis).2.2 = generatedEleventhPacket.2.2 := by
  rw [generatedEleventhPacket_actual]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
