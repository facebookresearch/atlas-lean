/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingOctadSourceTransport

/-! Actual incident octad-axis stabilizers project onto the genuine section/short flag group. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The actual first-axis stabilizer of the original old octad-image axis. -/
def generatedFeasibleContainingIncidentStabilizer :
    Subgroup (localAxisStabilizer generatedFeasibleContainingIncidentPair) :=
  MulAction.stabilizer (localAxisStabilizer generatedFeasibleContainingIncidentPair)
    (generatedOctadLocalAxis 0 0)

/-- Actual incident subgroup membership is exactly whole-vector fixation by the original action. -/
theorem generatedFeasibleContainingIncidentStabilizer_mem
    (h : localAxisStabilizer generatedFeasibleContainingIncidentPair) :
    h ∈ generatedFeasibleContainingIncidentStabilizer ↔
      rhoLocal h.val (generatedOctadLocalAxis 0 0) = generatedOctadLocalAxis 0 0 := Iff.rfl

/-- The genuine Co1 image of the incident E8 section and original fixed short line. -/
abbrev generatedFeasibleContainingIncidentFlag :=
  generatedAxisE8Co1ShortFlagStabilizer generatedOctadBasisOctad
    (Sum.inl (0, generatedFeasibleContainingIncidentPair))

/-- The old octad image has actual first short coordinate one at the incident root. -/
theorem generatedFeasibleContainingIncident_first_coordinate :
    (griessConwayEncode (generatedOctadLocalAxis 0 0)).2.1
      (Sum.inl (0, generatedFeasibleContainingIncidentPair)) = 1 := by
  rw [generatedOctadLocalAxis, generatedAxis_triality_octad_pair_coordinate,
    generatedFeasibleContainingIncidentPair_coordinates]
  have h8 : griessShortVector (Sum.inr (Sum.inl (generatedOctadBasisOctad, 0))) 8 =
      2 / Real.sqrt 8 := by
    change (griessShortIntegral generatedFeasibleOutsideOctadPrototypeLabel 8 : ℝ) /
      Real.sqrt 8 = _
    rw [generatedFeasibleOutsideOctadPrototype_integral]
    norm_num
  have h9 : griessShortVector (Sum.inr (Sum.inl (generatedOctadBasisOctad, 0))) 9 =
      2 / Real.sqrt 8 := by
    change (griessShortIntegral generatedFeasibleOutsideOctadPrototypeLabel 9 : ℝ) /
      Real.sqrt 8 = _
    rw [generatedFeasibleOutsideOctadPrototype_integral]
    norm_num
  rw [h8, h9]
  have hs : Real.sqrt 8 * Real.sqrt 8 = 8 := Real.mul_self_sqrt (by norm_num)
  norm_num
  field_simp
  nlinarith

/-- Whole octad fixation and incident preferred-root fixation force actual first phase zero. -/
theorem generatedFeasibleContainingIncident_first_phase_zero (f : localFiberSubgroup)
    (hfix : rhoLocal (localFiberIntoH f) (generatedOctadLocalAxis 0 0) =
      generatedOctadLocalAxis 0 0)
    (hp : griessShortPermutation f.val.2 (Sum.inl (0, generatedFeasibleContainingIncidentPair)) =
      Sum.inl (0, generatedFeasibleContainingIncidentPair)) :
    localShortPhase f (Sum.inl (0, generatedFeasibleContainingIncidentPair)) = 0 := by
  have hi := congrArg (fun x : GriessSpace => (griessConwayEncode x).2.1
    (Sum.inl (0, generatedFeasibleContainingIncidentPair))) hfix
  change (griessConwayEncode (localGriessRepresentation f _)).2.1 _ = _ at hi
  rw [localGriessRepresentation_encode, localConwayRawRepresentation_apply] at hi
  have hm := localShortOperator_image f (griessConwayEncode (generatedOctadLocalAxis 0 0)).2.1
    (Sum.inl (0, generatedFeasibleContainingIncidentPair))
  rw [hp] at hm
  change localShortOperator f (griessConwayEncode (generatedOctadLocalAxis 0 0)).2.1
    (Sum.inl (0, generatedFeasibleContainingIncidentPair)) = _ at hi
  rw [hm, generatedFeasibleContainingIncident_first_coordinate, mul_one] at hi
  exact (qSign_eq_one_iff _).mp hi

/-- Whole octad fixation and incident preferred-root fixation give the actual signed-axis fixer. -/
theorem generatedFeasibleContainingIncident_first_fixed (f : localFiberSubgroup)
    (hfix : rhoLocal (localFiberIntoH f) (generatedOctadLocalAxis 0 0) =
      generatedOctadLocalAxis 0 0)
    (hp : griessShortPermutation f.val.2 (Sum.inl (0, generatedFeasibleContainingIncidentPair)) =
      Sum.inl (0, generatedFeasibleContainingIncidentPair)) :
    localFiberIntoH f ∈ localAxisStabilizer generatedFeasibleContainingIncidentPair := by
  rw [localAxisStabilizer_mk_iff]
  exact ⟨hp, generatedFeasibleContainingIncident_first_phase_zero f hfix hp⟩

/-- Every actual incident octad-axis fixer projects into the genuine original section/short flag. -/
theorem generatedFeasibleContainingIncident_projection_mem
    (h : generatedFeasibleContainingIncidentStabilizer) :
    projH h.val.val ∈ generatedFeasibleContainingIncidentFlag := by
  obtain ⟨f, hf⟩ := QuotientGroup.mk'_surjective localDiagonalSubgroup h.val.val
  change localFiberIntoH f = h.val.val at hf
  have hfix : rhoLocal (localFiberIntoH f) (generatedOctadLocalAxis 0 0) =
      generatedOctadLocalAxis 0 0 := by rw [hf]; exact h.property
  have hfirst := h.val.property
  rw [← hf] at hfirst
  have hp := (localAxis_fiber_fixed_iff f generatedFeasibleContainingIncidentPair).mp hfirst
  have hs := generatedOctad_axis_stabilizer_spatial 0 0 f hfix
  refine ⟨f.val.2, ?_, ?_⟩
  · exact (generatedAxisE8ShortFlagStabilizer_mem _ _ f.val.2).mpr
      ⟨(generatedAxisE8SectionStabilizer_mem _ _).mp hs, hp.1⟩
  · change QuotientGroup.mk' signsSubgroup f.val.2 = projH h.val.val
    rw [← hf]
    rfl

/-- Restriction of the original local projection to the genuine incident flag subgroup. -/
def generatedFeasibleContainingIncidentProjection :
    generatedFeasibleContainingIncidentStabilizer →* generatedFeasibleContainingIncidentFlag :=
  (projH.comp ((localAxisStabilizer generatedFeasibleContainingIncidentPair).subtype.comp
    generatedFeasibleContainingIncidentStabilizer.subtype)).codRestrict _
      generatedFeasibleContainingIncident_projection_mem

/-- The restricted projection has the exact original H projection as its underlying value. -/
theorem generatedFeasibleContainingIncidentProjection_val
    (h : generatedFeasibleContainingIncidentStabilizer) :
    (generatedFeasibleContainingIncidentProjection h).val = projH h.val.val := rfl

/-- The restricted kernel condition is exactly the original H projection equation. -/
theorem generatedFeasibleContainingIncidentProjection_mem_ker_iff
    (h : generatedFeasibleContainingIncidentStabilizer) :
    h ∈ generatedFeasibleContainingIncidentProjection.ker ↔ projH h.val.val = 1 := by
  change generatedFeasibleContainingIncidentProjection h = 1 ↔ _
  constructor
  · exact fun hh => congrArg Subtype.val hh
  · intro hh
    exact Subtype.ext hh

/-- Every genuine incident flag admits a whole-axis-fixing lift whose actual first phase is zero. -/
theorem generatedFeasibleContainingIncidentProjection_surjective :
    Function.Surjective generatedFeasibleContainingIncidentProjection := by
  intro a
  obtain ⟨g, hg, hga⟩ := a.property
  have hp := (generatedAxisE8ShortFlagStabilizer_mem _ _ g).mp hg
  obtain ⟨f, hfg, hfix⟩ := generatedOctad_projected_stabilizer_lift 0 0 g hp.1
  have hfirst := generatedFeasibleContainingIncident_first_fixed f hfix (by rw [hfg]; exact hp.2)
  refine ⟨⟨⟨localFiberIntoH f, hfirst⟩, hfix⟩, Subtype.ext ?_⟩
  change projH (localFiberIntoH f) = a.val
  change QuotientGroup.mk' signsSubgroup f.val.2 = a.val
  rw [hfg]
  exact hga

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
