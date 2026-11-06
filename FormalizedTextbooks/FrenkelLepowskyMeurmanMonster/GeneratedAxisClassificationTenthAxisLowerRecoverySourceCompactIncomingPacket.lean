/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoverySourceCompactOrbit

/-! Entire genuine compact incoming and post-triality packets, without a source scalar anchor.
All symbolic proof bodies in this new module are uncompiled drafts. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

/-- The complete actual incoming Conway packet of the genuine compact source fiber. -/
def generatedTenthSourceCompactIncomingPacket : ConwayRawSpace :=
  griessConwayEncode
    (rhoLocal (localFiberIntoH generatedTenthSourceCompactFiber) generatedFifthAxis)

private theorem full_Q_incoming_matrix_short_equal (f g : localFiberSubgroup)
    (he : spinConjugation f.val.1 = spinConjugation g.val.1) (x : GriessSpace) :
    ((griessConwayEncode (rhoLocal (localFiberIntoH f) x)).1,
      (griessConwayEncode (rhoLocal (localFiberIntoH f) x)).2.1) =
    ((griessConwayEncode (rhoLocal (localFiberIntoH g) x)).1,
      (griessConwayEncode (rhoLocal (localFiberIntoH g) x)).2.1) := by
  let fields (y : GriessSpace) := ((griessConwayEncode y).1, (griessConwayEncode y).2.1)
  have hc (y : GriessSpace) : fields (localCentralGriess y) = fields y := by
    dsimp only [fields]
    rw [localCentralGriess_encode]
  change fields (rhoLocal (localFiberIntoH f) x) =
    fields (rhoLocal (localFiberIntoH g) x)
  rcases generatedTwelfth_full_Q_fiber_central_difference f g he with hh | hh
  · rw [hh]
  · rw [hh, map_mul, LinearEquiv.mul_apply]
    exact hc _

/-- Both incoming matrix and short fields equal those of the whole original Root02 packet.
The complete full-Q comparison removes the central tensor sign from these two fields. -/
theorem generatedTenth_source_compact_incoming_matrix_short :
    (generatedTenthSourceCompactIncomingPacket.1,
      generatedTenthSourceCompactIncomingPacket.2.1) =
    (generatedAxisGlobalFifthRoot02Packet.1, generatedAxisGlobalFifthRoot02Packet.2.1) := by
  have he := full_Q_incoming_matrix_short_equal
    (generatedAxisGlobalFifthShortWordFiber 2) generatedTenthSourceCompactFiber
    generatedTenth_source_compact_fiber_full_Q generatedFifthAxis
  have ho : griessConwayEncode
      (rhoLocal (localFiberIntoH (generatedAxisGlobalFifthShortWordFiber 2))
        generatedFifthAxis) = generatedAxisGlobalFifthRoot02Packet := by
    rw [generatedAxisGlobalFifthShortWordFiber_local]
    exact generatedAxisGlobalFifthRoot02Packet_actual
  unfold generatedTenthSourceCompactIncomingPacket
  exact he.symm.trans (congrArg (fun packet : ConwayRawSpace => (packet.1, packet.2.1)) ho)

/-- Every incoming matrix coordinate equals the actual original source matrix. -/
theorem generatedTenth_source_compact_incoming_matrix :
    generatedTenthSourceCompactIncomingPacket.1 = generatedAxisGlobalFifthRoot02Packet.1 :=
  congrArg (fun p : Matrix (Fin 24) (Fin 24) ℝ × (GriessShortIndex → ℝ) => p.1)
    generatedTenth_source_compact_incoming_matrix_short

/-- Every incoming signed short coordinate equals the actual original source short coefficient. -/
theorem generatedTenth_source_compact_incoming_short :
    generatedTenthSourceCompactIncomingPacket.2.1 =
      generatedAxisGlobalFifthRoot02Packet.2.1 :=
  congrArg (fun p : Matrix (Fin 24) (Fin 24) ℝ × (GriessShortIndex → ℝ) => p.2)
    generatedTenth_source_compact_incoming_matrix_short

/-- All4096 by24 incoming tensor coefficients are the genuine compact tensor action on
all actual Fifth tensor coefficients. No original source scalar calibration is required. -/
theorem generatedTenth_source_compact_incoming_packet_tensor :
    generatedTenthSourceCompactIncomingPacket.2.2 =
      generatedTenthAxisLowerRecoverySourceCompactTensor
        (griessConwayEncode generatedFifthAxis).2.2 := by
  unfold generatedTenthSourceCompactIncomingPacket
  change (griessConwayEncode
    (localGriessRepresentation generatedTenthSourceCompactFiber generatedFifthAxis)).2.2 = _
  rw [localGriessRepresentation_encode, localConwayRawRepresentation_apply,
    generatedTenth_source_compact_fiber_tensor]

/-- The complete genuine post-triality packet retains every field and its full normalization. -/
def generatedTenthSourceCompactFinalPacket : ConwayRawSpace :=
  generatedAxisGlobalRawTrialityFormula generatedTenthSourceCompactIncomingPacket

/-- The complete post-triality packet is the actual encoded compact-source axis. -/
theorem generatedTenth_source_compact_final_packet_actual :
    griessConwayEncode generatedTenthSourceCompactAxis =
      generatedTenthSourceCompactFinalPacket := by
  unfold generatedTenthSourceCompactFinalPacket generatedTenthSourceCompactIncomingPacket
  rw [generatedTenth_source_compact_axis_expression,
    generatedAxisGlobalRawTrialityFormula_actual]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
