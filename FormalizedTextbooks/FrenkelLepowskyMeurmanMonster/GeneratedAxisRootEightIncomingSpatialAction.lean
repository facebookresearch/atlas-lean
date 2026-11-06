/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightIncomingSpatialData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechBinaryFaithfulness

/-! An actual compatible incoming fiber uses the explicit positive original spatial word. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

/-- Each complete original positive incoming unit column has its exact rational coordinates. -/
theorem generatedRootEight_incoming_positive_spatial_unit (r : Fin 8) (i : Fin 24) :
    (generatedAxisGlobalFifthShortSpatialWord 8).val
      (Pi.single (generatedTwelfthTensorSourceCoordinate r) 1) i =
      (generatedRootEightIncomingSpatialNumerator r i : ℝ) / 4 := by
  rw [show (generatedAxisGlobalFifthShortSpatialWord 8).val
      (Pi.single (generatedTwelfthTensorSourceCoordinate r) 1) i =
      leechIsomMatrix (generatedAxisGlobalFifthShortSpatialWord 8) i
        (generatedTwelfthTensorSourceCoordinate r) from rfl,
    generatedFifthRootEight_forward_matrix_coordinate,
    generatedRootEight_incoming_spatial_frame_certificate, Int.cast_mul, Int.cast_ofNat]
  ring

/-- The complete chosen source spatial lift has the same actual Conway class as the positive word. -/
theorem generatedRootEight_incoming_positive_spatial_projection :
    QuotientGroup.mk' signsSubgroup (generatedTenthQWordFiber 8).val.2 =
      QuotientGroup.mk' signsSubgroup (generatedAxisGlobalFifthShortSpatialWord 8) := by
  change projH (localFiberIntoH (generatedTenthQWordFiber 8)) = _
  rw [generatedTenth_Q_word_fiber_local]
  exact generatedAxisGlobalFifthShortLocalWord_projection 8

/-- Full original Q agreement makes the explicitly positive spin and spatial pair compatible. -/
theorem generatedRootEight_incoming_positive_compatibility :
    spinBinaryAction (generatedRootEightIncomingCompactSpin 0) =
      leechBinaryAction (generatedAxisGlobalFifthShortSpatialWord 8) := by
  have hp := congrArg co1BinaryAction generatedRootEight_incoming_positive_spatial_projection
  change leechBinaryAction (generatedTenthQWordFiber 8).val.2 =
    leechBinaryAction (generatedAxisGlobalFifthShortSpatialWord 8) at hp
  exact generatedRootEight_incoming_compact_compatibility.trans hp

/-- The full incoming compact spin paired with the explicit genuine positive original isometry. -/
def generatedRootEightIncomingPositiveFiber : localFiberSubgroup :=
  ⟨(generatedRootEightIncomingCompactSpin 0, generatedAxisGlobalFifthShortSpatialWord 8),
    generatedRootEight_incoming_positive_compatibility⟩

/-- The explicitly positive incoming transport is a genuine full local element. -/
def generatedRootEightIncomingPositiveLocal : H :=
  localFiberIntoH generatedRootEightIncomingPositiveFiber

/-- The positive local transport retains the exact actual original projection. -/
theorem generatedRootEight_incoming_positive_projection :
    projH generatedRootEightIncomingPositiveLocal = projH generatedFifthRootEightLocal := by
  change QuotientGroup.mk' signsSubgroup (generatedAxisGlobalFifthShortSpatialWord 8) = _
  exact (generatedAxisGlobalFifthShortLocalWord_projection 8).symm

/-- The entire positive incoming Griess vector under its actual local transport. -/
def generatedRootEightIncomingPositiveDestination : GriessSpace :=
  rhoLocal generatedRootEightIncomingPositiveLocal generatedFifthAxis

/-- The actual final triality destination of the complete positive incoming vector. -/
def generatedRootEightIncomingPositiveTrialityDestination : GriessSpace :=
  sExtra generatedRootEightIncomingPositiveDestination

/-- The complete positive incoming matrix and signed-short blocks equal the actual original packet. -/
theorem generatedRootEight_incoming_positive_matrix_short :
    (griessConwayEncode generatedRootEightIncomingPositiveDestination).1 =
        generatedAxisGlobalFifthRoot08Packet.1 ∧
    (griessConwayEncode generatedRootEightIncomingPositiveDestination).2.1 =
        generatedAxisGlobalFifthRoot08Packet.2.1 := by
  have ht := generatedTwelfth_full_Q_matrix_short_blocks generatedRootEightIncomingPositiveFiber
    (generatedTenthQWordFiber 8) generatedRootEight_incoming_compact_source_conjugation
    generatedFifthAxis
  rw [generatedTenth_Q_word_fiber_local, generatedAxisGlobalFifthRoot08Packet_actual] at ht
  exact ht

/-- A genuine local element of trivial projection connects the full final positive and original axes. -/
theorem generatedRootEight_incoming_positive_projection_orbit :
    ∃ u : H, projH u = 1 ∧ generatedFifthRootEightAxis =
      rhoLocal u generatedRootEightIncomingPositiveTrialityDestination := by
  exact generatedRootEight_incoming_central_projection_orbit
    generatedRootEightIncomingPositiveFiber generatedRootEight_incoming_compact_source_conjugation

/-- Every actual whole positive-axis fixer transfers with its projection to the original axis. -/
theorem generatedRootEight_incoming_positive_fixer_transfer (h : H)
    (hfix : rhoLocal h generatedRootEightIncomingPositiveTrialityDestination =
      generatedRootEightIncomingPositiveTrialityDestination) :
    ∃ k : H, projH k = projH h ∧
      rhoLocal k generatedFifthRootEightAxis = generatedFifthRootEightAxis := by
  exact generatedRootEight_incoming_central_fixer_transfer generatedRootEightIncomingPositiveFiber
    generatedRootEight_incoming_compact_source_conjugation h hfix

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
