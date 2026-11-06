/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMonomialAxisFixed
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMonomialSignGeneration

/-! Genuine fourth-axis stabilizing lifts of every actual equal-pair Golay sign class. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Physical isometries whose actual Co1 class has a genuine full-axis stabilizing lift. -/
def generatedFourthPhysicalAxisProjection : Subgroup leechIsomSubgroup :=
  (generatedFourthLocalAxisStabilizer.map projH).comap (QuotientGroup.mk' signsSubgroup)

/-- Each genuine corrected monomial word has precisely its original physical projection. -/
theorem generatedFourth_monomial_physical_projection_mem (k : Fin 4) :
    (generatedFourthMonomialFiber k).val.2 ∈ generatedFourthPhysicalAxisProjection := by
  change (QuotientGroup.mk' signsSubgroup) (generatedFourthMonomialFiber k).val.2 ∈
    generatedFourthLocalAxisStabilizer.map projH
  refine ⟨localFiberIntoH (generatedFourthMonomialCorrectedFiber k),
    generatedFourth_monomial_axis_fixed k, ?_⟩
  change (QuotientGroup.mk' signsSubgroup) (generatedFourthMonomialCorrectedFiber k).val.2 = _
  rw [generatedFourth_monomial_corrected_spatial]

/-- The original cube sign has a genuine full-axis stabilizing lift, with no phase assumption. -/
theorem generatedFourth_monomial_cube_physical_projection_mem :
    golaySignIsometry generatedFourthFlagCubeSignCode ∈ generatedFourthPhysicalAxisProjection := by
  obtain ⟨f, hf, ha⟩ := generatedFourth_flag_cube_sign_axis_lift
  change (QuotientGroup.mk' signsSubgroup) (golaySignIsometry generatedFourthFlagCubeSignCode) ∈
    generatedFourthLocalAxisStabilizer.map projH
  refine ⟨localFiberIntoH f, ha, ?_⟩
  change (QuotientGroup.mk' signsSubgroup) f.val.2 = _
  rw [hf]

/-- The actual normalized flag generator has a genuine full-axis stabilizing lift. -/
theorem generatedFourth_monomial_normalized_projection_mem :
    generatedFourthFlagNormalizedLift.val.2 ∈ generatedFourthPhysicalAxisProjection := by
  change (QuotientGroup.mk' signsSubgroup) generatedFourthFlagNormalizedLift.val.2 ∈
    generatedFourthLocalAxisStabilizer.map projH
  refine ⟨localFiberIntoH generatedFourthFlagCorrectedLift,
    generatedFourth_flag_corrected_lift_axis_fixed, ?_⟩
  change (QuotientGroup.mk' signsSubgroup) generatedFourthFlagCorrectedLift.val.2 = _
  rw [generatedFourth_flag_corrected_lift_spatial]

/-- Physical closure of the four actual monomial words and the actual normalized flag generator. -/
def generatedFourthPhysicalFlagGeneratorSubgroup : Subgroup leechIsomSubgroup :=
  Subgroup.closure (Set.range (fun k : Fin 4 => (generatedFourthMonomialFiber k).val.2) ∪
    {generatedFourthFlagNormalizedLift.val.2})

/-- Every element of the genuine proposed flag-generator closure has an actual stabilizing lift. -/
theorem generatedFourth_monomial_flag_generated_le_projection :
    generatedFourthPhysicalFlagGeneratorSubgroup ≤ generatedFourthPhysicalAxisProjection := by
  apply (Subgroup.closure_le _).mpr
  rintro e (⟨k, rfl⟩ | rfl)
  · exact generatedFourth_monomial_physical_projection_mem k
  · exact generatedFourth_monomial_normalized_projection_mem

/-- Every Co1 class in the genuine physical closure has an actual full-axis stabilizing lift. -/
theorem generatedFourth_monomial_physical_subgroup_le_projection :
    generatedFourthMonomialPhysicalSubgroup ≤ generatedFourthPhysicalAxisProjection := by
  apply (Subgroup.closure_le _).mpr
  rintro e (⟨k, rfl⟩ | rfl)
  · exact generatedFourth_monomial_physical_projection_mem k
  · exact generatedFourth_monomial_cube_physical_projection_mem

/-- Every genuine equal-pair Golay sign class has an actual full-axis stabilizing lift. -/
theorem generatedFourth_monomial_equal_sign_axis_lift (c : golayCode)
    (hc : c.val 8 = c.val 11) :
    ∃ h : H, rhoLocal h generatedFourthAxis = generatedFourthAxis ∧
      projH h = (QuotientGroup.mk' signsSubgroup) (golaySignIsometry c) := by
  have hm := generatedFourth_monomial_physical_subgroup_le_projection
    (generatedFourth_monomial_equal_sign_mem c hc)
  exact hm

/-- The actual equal-sign subgroup projects wholly into the genuine full-axis stabilizer image. -/
theorem generatedFourth_monomial_equal_sign_subgroup_le_projection :
    generatedFourthFlagEqualSignSubgroup ≤ generatedFourthPhysicalAxisProjection :=
  generatedFourth_monomial_equal_sign_subgroup_le.trans
    generatedFourth_monomial_physical_subgroup_le_projection

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
