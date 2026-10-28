/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleOddDestinationFlagStabilizer

/-! Actual orthogonal odd-axis stabilizers project onto the genuine frame/root flag group. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The actual first-axis stabilizer of the original old odd-image axis. -/
def generatedFeasibleOddDestinationStabilizer :
    Subgroup (localAxisStabilizer generatedFeasibleOddDestinationPair) :=
  MulAction.stabilizer (localAxisStabilizer generatedFeasibleOddDestinationPair)
    (generatedOddAxis)

/-- Actual orthogonal subgroup membership is whole-vector fixation by the original action. -/
theorem generatedFeasibleOddDestinationStabilizer_mem
    (h : localAxisStabilizer generatedFeasibleOddDestinationPair) :
    h ∈ generatedFeasibleOddDestinationStabilizer ↔
      rhoLocal h.val (generatedOddAxis) = generatedOddAxis := Iff.rfl

/-- The genuine Co1 image of the original frame and fixed preferred root. -/
abbrev generatedFeasibleOddDestinationFlag := generatedFeasibleOddFrameCo1FlagStabilizer

/-- The original odd axis has nonzero actual first short coordinate one quarter. -/
theorem generatedFeasibleOddDestination_first_coordinate :
    (griessConwayEncode generatedOddAxis).2.1
      (Sum.inl (0, generatedFeasibleOddDestinationPair)) = (1 / 4 : ℝ) := by
  rw [generatedOddAxis, generatedAxis_triality_odd_pair_coordinate,
    generatedFeasibleOddDestinationPair_coordinates]
  have hm : golayEncodedMask 0 = 0 := by decide +kernel
  simp only [griessShortVector, griessShortIntegral, Fin.val_zero, hm,
    Nat.zero_testBit, Bool.false_eq_true, ite_false, one_mul]
  norm_num
  have hs : Real.sqrt 8 * Real.sqrt 8 = 8 := Real.mul_self_sqrt (by norm_num)
  field_simp
  nlinarith

/-- Whole odd fixation and orthogonal preferred-root fixation force actual first phase zero. -/
theorem generatedFeasibleOddDestination_first_phase_zero (f : localFiberSubgroup)
    (hfix : rhoLocal (localFiberIntoH f) (generatedOddAxis) =
      generatedOddAxis)
    (hp : griessShortPermutation f.val.2 (Sum.inl (0, generatedFeasibleOddDestinationPair)) =
      Sum.inl (0, generatedFeasibleOddDestinationPair)) :
    localShortPhase f (Sum.inl (0, generatedFeasibleOddDestinationPair)) = 0 := by
  have hi := congrArg (fun x : GriessSpace => (griessConwayEncode x).2.1
    (Sum.inl (0, generatedFeasibleOddDestinationPair))) hfix
  change (griessConwayEncode (localGriessRepresentation f _)).2.1 _ = _ at hi
  rw [localGriessRepresentation_encode, localConwayRawRepresentation_apply] at hi
  have hm := localShortOperator_image f (griessConwayEncode (generatedOddAxis)).2.1
    (Sum.inl (0, generatedFeasibleOddDestinationPair))
  rw [hp] at hm
  change localShortOperator f (griessConwayEncode (generatedOddAxis)).2.1
    (Sum.inl (0, generatedFeasibleOddDestinationPair)) = _ at hi
  rw [hm, generatedFeasibleOddDestination_first_coordinate] at hi
  have hsign : qSign (localShortPhase f (Sum.inl (0, generatedFeasibleOddDestinationPair))) =
      1 := by nlinarith only [hi]
  exact (qSign_eq_one_iff _).mp hsign

/-- Whole odd fixation and orthogonal preferred-root fixation give the actual signed-axis fixer. -/
theorem generatedFeasibleOddDestination_first_fixed (f : localFiberSubgroup)
    (hfix : rhoLocal (localFiberIntoH f) (generatedOddAxis) =
      generatedOddAxis)
    (hp : griessShortPermutation f.val.2 (Sum.inl (0, generatedFeasibleOddDestinationPair)) =
      Sum.inl (0, generatedFeasibleOddDestinationPair)) :
    localFiberIntoH f ∈ localAxisStabilizer generatedFeasibleOddDestinationPair := by
  rw [localAxisStabilizer_mk_iff]
  exact ⟨hp, generatedFeasibleOddDestination_first_phase_zero f hfix hp⟩

/-- Every actual orthogonal odd-axis fixer projects into the genuine original frame/root flag. -/
theorem generatedFeasibleOddDestination_projection_mem
    (h : generatedFeasibleOddDestinationStabilizer) :
    projH h.val.val ∈ generatedFeasibleOddDestinationFlag := by
  obtain ⟨f, hf⟩ := QuotientGroup.mk'_surjective localDiagonalSubgroup h.val.val
  change localFiberIntoH f = h.val.val at hf
  have hfix : rhoLocal (localFiberIntoH f) (generatedOddAxis) =
      generatedOddAxis := by rw [hf]; exact h.property
  have hfirst := h.val.property
  rw [← hf] at hfirst
  have hp := (localAxis_fiber_fixed_iff f generatedFeasibleOddDestinationPair).mp hfirst
  have hs := generatedOdd_axis_stabilizer_spatial f hfix
  refine ⟨f.val.2, ?_, ?_⟩
  · exact ⟨hs, hp.1⟩
  · change QuotientGroup.mk' signsSubgroup f.val.2 = projH h.val.val
    rw [← hf]
    rfl

/-- Restriction of the original local projection to the genuine orthogonal flag subgroup. -/
def generatedFeasibleOddDestinationProjection :
    generatedFeasibleOddDestinationStabilizer →* generatedFeasibleOddDestinationFlag :=
  (projH.comp ((localAxisStabilizer generatedFeasibleOddDestinationPair).subtype.comp
    generatedFeasibleOddDestinationStabilizer.subtype)).codRestrict _
      generatedFeasibleOddDestination_projection_mem

/-- The restricted projection has the exact original H projection as its underlying value. -/
theorem generatedFeasibleOddDestinationProjection_val
    (h : generatedFeasibleOddDestinationStabilizer) :
    (generatedFeasibleOddDestinationProjection h).val = projH h.val.val := rfl

/-- The restricted kernel condition is exactly the original H projection equation. -/
theorem generatedFeasibleOddDestinationProjection_mem_ker_iff
    (h : generatedFeasibleOddDestinationStabilizer) :
    h ∈ generatedFeasibleOddDestinationProjection.ker ↔ projH h.val.val = 1 := by
  change generatedFeasibleOddDestinationProjection h = 1 ↔ _
  constructor
  · exact fun hh => congrArg Subtype.val hh
  · intro hh
    exact Subtype.ext hh

/-- Every genuine orthogonal flag admits a whole-axis-fixing lift with actual first phase zero. -/
theorem generatedFeasibleOddDestinationProjection_surjective :
    Function.Surjective generatedFeasibleOddDestinationProjection := by
  intro a
  obtain ⟨g, hg, hga⟩ := a.property
  have hp := hg
  obtain ⟨f, hfg, hfix⟩ := generatedOddAxis_projected_stabilizer_lift g hp.1
  have hfirst := generatedFeasibleOddDestination_first_fixed f hfix (by rw [hfg]; exact hp.2)
  refine ⟨⟨⟨localFiberIntoH f, hfirst⟩, hfix⟩, Subtype.ext ?_⟩
  change projH (localFiberIntoH f) = a.val
  change QuotientGroup.mk' signsSubgroup f.val.2 = a.val
  rw [hfg]
  exact hga

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
