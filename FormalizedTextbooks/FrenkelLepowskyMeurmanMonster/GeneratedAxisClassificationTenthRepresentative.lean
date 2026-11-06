/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthRoot02Packet
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthPhaseRoots

/-! A genuine further fifth-axis transition. The ordinal names select literal
words; identifying a descriptive source class and counting its stabilizer are
separate mathematical tasks. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
-- The literal seven-stage original word has a deep elaboration spine.
set_option maxRecDepth 10000

/-- The original phase-preserving local normalization at binary root 2. -/
def generatedTenthLocal : H := generatedAxisGlobalFifthShortLocalWord 2

/-- The literal original local word followed by the original triality generator. -/
def generatedTenthAxisWord : ↥G :=
  extraIntoGenerated * localIntoGenerated generatedTenthLocal * generatedFifthAxisWord

/-- This prototype is an actual word image of the original signed octad axis. -/
def generatedTenthAxis : GriessSpace :=
  generatedTenthAxisWord.val
    (conwayShortAxis (Sum.inr (Sum.inl (generatedFourthOctad, 0))) 0)

/-- The literal generated-group word agrees with the original local/triality action. -/
theorem generatedTenthAxis_local_expression :
    generatedTenthAxis = sExtra (rhoLocal generatedTenthLocal generatedFifthAxis) := by
  rfl

/-- The entire original Conway packet includes every matrix, short and tensor coordinate. -/
def generatedTenthPacket : ConwayRawSpace :=
  generatedAxisGlobalRawTrialityFormula generatedAxisGlobalFifthRoot02Packet

/-- No constituent or central phase is omitted from this actual prototype packet. -/
theorem generatedTenthPacket_actual :
    griessConwayEncode generatedTenthAxis = generatedTenthPacket := by
  exact generatedAxisGlobalFifthRoot02Packet_triality

/-- The actual prototype is in the global orbit of every original signed-short axis. -/
theorem generatedTenthAxis_mem_generatedOrbit (r : GriessShortIndex) (c : ZMod 2) :
    generatedTenthAxis ∈ generatedVectorOrbit (conwayShortAxis r c) := by
  obtain ⟨h, hh⟩ := generatedAxis_local_signed_transitive r
    (Sum.inr (Sum.inl (generatedFourthOctad, 0))) c 0
  refine ⟨generatedTenthAxisWord * localIntoGenerated h, ?_⟩
  change generatedTenthAxisWord.val (rhoLocal h (conwayShortAxis r c)) = _
  rw [hh]
  rfl

/-- The inverse-triality output at the identical root has the same full-axis local orbit. -/
theorem generatedTenthAxis_inverse_local_orbit :
    ∃ h : H, generatedTenthAxis =
      rhoLocal h (sExtra⁻¹ (rhoLocal generatedTenthLocal generatedFifthAxis)) := by
  exact generatedAxisGlobalFifthMergedRoot_orbit 0

/-- The actual original matrix coordinates are precisely the matrix of the complete packet. -/
theorem generatedTenth_matrix :
    (griessConwayEncode generatedTenthAxis).1 = generatedTenthPacket.1 := by
  rw [generatedTenthPacket_actual]

/-- The actual signed-short coordinates are precisely those of the complete packet. -/
theorem generatedTenth_short :
    (griessConwayEncode generatedTenthAxis).2.1 = generatedTenthPacket.2.1 := by
  rw [generatedTenthPacket_actual]

/-- All 98,304 original physical tensor coordinates retain the full source normalization. -/
theorem generatedTenth_tensor :
    (griessConwayEncode generatedTenthAxis).2.2 = generatedTenthPacket.2.2 := by
  rw [generatedTenthPacket_actual]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
