/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthSpatialStabilizer
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthPlaneGeometry
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthFinalPairCoordinates

/-! Every actual whole-axis fixer of the counted sixth prototype fixes its rooted pair axis.
The spatial flag fixes the short label on coordinates sixteen and seventeen, and the
nonzero final short coefficient 13/32 forces the phase to vanish. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The rooted short label of the sixth flag is the positive target pair label. -/
theorem generatedFeasibleSixthSlot_plane_short_eq :
    generatedSixthPlaneShort = Sum.inl (0, generatedSixthTargetPair 0) := rfl

/-- The complete integer numerator of the rooted final short coefficient is thirteen. -/
theorem generatedFeasibleSixthSlot_root_numerator :
    generatedSixthFinalPairNumerator 0 (generatedSixthTargetPair 0) = 13 := by
  unfold generatedSixthFinalPairNumerator
  rw [(generatedSixth_pair_coordinate_certificate 0).2]
  decide

/-- The actual final sixth-axis short coefficient on the rooted label is 13/32. -/
theorem generatedFeasibleSixthSlot_root_coefficient :
    (griessConwayEncode generatedSixthAxis).2.1 generatedSixthPlaneShort = 13 / 32 := by
  rw [generatedFeasibleSixthSlot_plane_short_eq, generatedSixth_final_pair_coordinate,
    generatedFeasibleSixthSlot_root_numerator]
  norm_num

/-- Every actual local fixer of the sixth prototype fixes both signs of its rooted pair axis:
the entire stabilizer lies in the actual local stabilizer of that positive pair axis. -/
theorem generatedFeasibleSixthSlot_stabilizer_le_root :
    generatedSixthLocalAxisStabilizer ≤ localAxisStabilizer (generatedSixthTargetPair 0) := by
  intro h hh
  obtain ⟨f, hf⟩ := QuotientGroup.mk'_surjective localDiagonalSubgroup h
  change localFiberIntoH f = h at hf
  have hfix : rhoLocal (localFiberIntoH f) generatedSixthAxis = generatedSixthAxis := by
    rw [hf]
    exact hh
  have hperm := ((generatedSixthSpatialStabilizer_mem f.val.2).mp
    (generatedSixth_local_fiber_spatial_mem f hfix)).2
  have hcoord := congrFun (generatedFourth_local_short f generatedSixthAxis)
    generatedSixthPlaneShort
  rw [hfix] at hcoord
  have himage := localShortOperator_image f (griessConwayEncode generatedSixthAxis).2.1
    generatedSixthPlaneShort
  rw [hperm, ← hcoord, generatedFeasibleSixthSlot_root_coefficient] at himage
  have hq : qSign (localShortPhase f generatedSixthPlaneShort) = 1 := by linarith
  have hphase := (qSign_eq_one_iff _).mp hq
  rw [← hf]
  exact (localAxisStabilizer_mk_iff f _).mpr ⟨hperm, hphase⟩

/-- Consequently every actual sixth-axis fixer fixes each signed rooted pair axis. -/
theorem generatedFeasibleSixthSlot_stabilizer_fixes_root (h : H)
    (hh : h ∈ generatedSixthLocalAxisStabilizer) (c : ZMod 2) :
    rhoLocal h (conwayShortAxis (Sum.inl (0, generatedSixthTargetPair 0)) c) =
      conwayShortAxis (Sum.inl (0, generatedSixthTargetPair 0)) c :=
  localAxisStabilizer_signedAxis_fixed h _ (generatedFeasibleSixthSlot_stabilizer_le_root hh) c

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
