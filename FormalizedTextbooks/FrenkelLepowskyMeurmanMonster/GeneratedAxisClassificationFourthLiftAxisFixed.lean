/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftShortFixed
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftMatrixFixed
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFourthStabilizerProjection

/-! A genuine full-axis stabilizing lift of the corrected physical flag generator. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The corrected genuine local lift fixes the entire original fourth axis. -/
theorem generatedFourth_flag_corrected_lift_axis_fixed :
    rhoLocal (localFiberIntoH generatedFourthFlagCorrectedLift) generatedFourthAxis =
      generatedFourthAxis :=
  generatedFourth_flag_corrected_lift_fixed_of_short generatedFourth_flag_corrected_lift_short_fixed

/-- The original corrected flag lift, now in the genuine full-axis H stabilizer. -/
def generatedFourthFlagAxisLift : generatedFourthLocalAxisStabilizer :=
  ⟨localFiberIntoH generatedFourthFlagCorrectedLift,
    generatedFourth_flag_corrected_lift_axis_fixed⟩

/-- The actual Co1 class of the normalized physical flag generator, with genuine flag membership. -/
def generatedFourthFlagLiftProjection :
    generatedAxisE8Co1ShortFlagStabilizer generatedFourthFlagOctad generatedFourthFlagShort :=
  ⟨(QuotientGroup.mk' signsSubgroup) generatedFourthFlagNormalizedLift.val.2,
    ⟨generatedFourthFlagNormalizedLift.val.2, generatedFourth_flag_lift_mem, rfl⟩⟩

/-- The full-axis lift projects to the exact original normalized physical flag generator. -/
theorem generatedFourth_flag_axis_lift_projection :
    generatedFourthLocalAxisProjection generatedFourthFlagAxisLift =
      generatedFourthFlagLiftProjection := by
  apply Subtype.ext
  change projH (localFiberIntoH generatedFourthFlagCorrectedLift) =
    (QuotientGroup.mk' signsSubgroup) generatedFourthFlagNormalizedLift.val.2
  change (QuotientGroup.mk' signsSubgroup) generatedFourthFlagCorrectedLift.val.2 = _
  rw [generatedFourth_flag_corrected_lift_spatial]

/-- The genuine normalized flag generator lies in the actual full-axis projected stabilizer. -/
theorem generatedFourth_flag_lift_projection_mem_range :
    generatedFourthFlagLiftProjection ∈ generatedFourthLocalAxisProjection.range :=
  ⟨generatedFourthFlagAxisLift, generatedFourth_flag_axis_lift_projection⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
