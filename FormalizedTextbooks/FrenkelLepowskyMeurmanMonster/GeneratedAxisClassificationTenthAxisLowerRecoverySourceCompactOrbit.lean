/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoverySourceCompactFiber
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthFullQCentralDifference
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthRepresentative
public import Mathlib.GroupTheory.GroupAction.Basic

/-! The genuine compact source gives the same actual local orbit after triality.
The original spin's scalar orientation is unnecessary for this orbit identity. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 100000

/-- The chosen compact source axis uses actual local and triality actions throughout. -/
@[irreducible] def generatedTenthSourceCompactAxis : GriessSpace :=
  sExtra (rhoLocal (localFiberIntoH generatedTenthSourceCompactFiber) generatedFifthAxis)

/-- This names the complete Griess action without choosing the original central phase. -/
theorem generatedTenth_source_compact_axis_expression :
    generatedTenthSourceCompactAxis =
      sExtra (rhoLocal (localFiberIntoH generatedTenthSourceCompactFiber)
        generatedFifthAxis) := by
  unfold generatedTenthSourceCompactAxis
  rfl

/-- The original full source and the genuine compact source have identical full Q actions. -/
theorem generatedTenth_source_compact_fiber_full_Q :
    spinConjugation (generatedAxisGlobalFifthShortWordFiber 2).val.1 =
      spinConjugation generatedTenthSourceCompactFiber.val.1 := by
  have h := MulEquiv.ext generatedTenth_source_q_certificates_original_Q_eq
  have hc := congrArg (fun p : SpinHolomorph × leechIsomSubgroup => spinConjugation p.1)
    generatedTenth_source_compact_fiber_components
  exact h.trans hc.symm

/-- The entire original Tenth axis lies in the actual local orbit of the compact source axis. -/
theorem generatedTenth_source_compact_axis_local_orbit :
    ∃ h : H, generatedTenthAxis = rhoLocal h generatedTenthSourceCompactAxis := by
  have h := generatedTwelfth_full_Q_triality_local_orbit
    (generatedAxisGlobalFifthShortWordFiber 2) generatedTenthSourceCompactFiber
    generatedTenth_source_compact_fiber_full_Q generatedFifthAxis
  rw [generatedAxisGlobalFifthShortWordFiber_local] at h
  rw [generatedTenthAxis_local_expression, generatedTenth_source_compact_axis_expression]
  exact h

/-- The compact source stabilizer is the full genuine local stabilizer of its whole axis. -/
def generatedTenthSourceCompactAxisStabilizer : Subgroup H :=
  MulAction.stabilizer H generatedTenthSourceCompactAxis

private theorem stabilizer_card_of_action (a b : GriessSpace)
    (h : ∃ g : H, b = rhoLocal g a) :
    Nat.card (MulAction.stabilizer H a) = Nat.card (MulAction.stabilizer H b) := by
  obtain ⟨g, hg⟩ := h
  have hs : b = g • a := hg
  exact Nat.card_congr (MulAction.stabilizerEquivStabilizer hs).toEquiv

/-- Whole-axis stabilizer cardinality transfers through the actual local conjugacy. -/
theorem generatedTenth_source_compact_axis_stabilizer_card :
    Nat.card generatedTenthSourceCompactAxisStabilizer =
      Nat.card (MulAction.stabilizer H generatedTenthAxis) :=
  stabilizer_card_of_action generatedTenthSourceCompactAxis generatedTenthAxis
    generatedTenth_source_compact_axis_local_orbit

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
