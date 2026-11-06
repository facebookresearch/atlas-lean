/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingEighthActualOrbitCount
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleTransitionReciprocity

/-! The exact entire containing-to-one-eighth transition and its genuine reciprocal entry. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

/-- An actual one-eighth output is necessarily in the entire noncoordinate input remainder. -/
theorem generatedFeasibleContaining_eighth_output_noncoordinate
    (h : localAxisStabilizer generatedFeasiblePhysicalRootPair)
    (hc : generatedFeasibleContainingInputFirst
      (Quotient.mk (QuotientGroup.rightRel
        (localFeasibleTransitionSubgroup generatedFeasiblePhysicalRootPair)) h) = 1 / 8) :
    Quotient.mk (QuotientGroup.rightRel
      (localFeasibleTransitionSubgroup generatedFeasiblePhysicalRootPair)) h ∈
        generatedFeasibleContainingNoncoordinateInputCosets := by
  let x := rhoLocal h.val generatedFeasibleContainingOctadDestination
  have hx : x ∈ MulAction.orbit (localAxisStabilizer generatedFeasiblePhysicalRootPair)
      generatedFeasibleContainingOctadDestination := ⟨h, rfl⟩
  have hz : (griessConwayEncode x).2.1 generatedFeasibleMateLabel = 0 := by
    by_contra hn
    have hd := generatedFeasibleContaining_mate_nonzero_diagonal_one x hx hn
    have hp := generatedFeasibleContaining_first_diagonal_relation x hx
    have hf := generatedFeasibleContaining_first_coordinate x hx
    rw [generatedFeasibleContainingInputFirst_apply,
      generatedFeasibleContaining_triality_first_coordinate] at hc
    change (griessConwayEncode x).1 0 1 +
      ((griessConwayEncode x).2.1 (Sum.inl (0, generatedFeasiblePhysicalRootPair)) -
        (griessConwayEncode x).2.1 generatedFeasibleMateLabel) / 2 = 1 / 8 at hc
    rw [hf] at hc
    rcases generatedFeasibleContaining_short_unit x hx generatedFeasibleMateLabel with hu | hzero
    · nlinarith
    · exact hn hzero
  exact (generatedFeasibleContaining_noncoordinate_input_word_iff h).mpr ⟨hx, hz⟩

/-- The entire actual transition receives precisely the proved 64,512-input fibre.
There are no additional coordinate inputs in this actual class. -/
theorem generatedFeasibleActualTransition_containing_eighth_cosets :
    generatedFeasibleActualTransitionCosets generatedFeasiblePhysicalRootPair
      generatedFeasibleContainingOctadDestination generatedFeasibleContainingNewDestination =
        generatedFeasibleContainingOutgoingCoefficientInputs 1 := by
  ext c
  constructor
  · intro hc
    have he : generatedFeasibleTransitionDestination generatedFeasiblePhysicalRootPair
        generatedFeasibleContainingOctadDestination c =
          generatedFeasibleSecondaryAClass generatedFeasibleContainingNewDestination := hc
    have hf : generatedFeasibleContainingInputFirst c = 1 / 8 := by
      change generatedFeasibleContainingAClassFirst
        (generatedFeasibleTransitionDestination generatedFeasiblePhysicalRootPair
          generatedFeasibleContainingOctadDestination c) = _
      rw [he]
      exact generatedFeasibleContainingNewDestination_first_coordinate
    refine ⟨?_, hf⟩
    induction c using Quotient.inductionOn with
    | h h => exact generatedFeasibleContaining_eighth_output_noncoordinate h hf
  · intro hc
    exact generatedFeasibleContaining_eighth_input_recognition c hc

/-- The genuine containing-to-sixth transition has exactly 64,512 actual cosets. -/
theorem generatedFeasibleActualTransition_containing_eighth_card :
    Nat.card (generatedFeasibleActualTransitionCosets generatedFeasiblePhysicalRootPair
      generatedFeasibleContainingOctadDestination generatedFeasibleContainingNewDestination) =
        64512 := by
  rw [generatedFeasibleActualTransition_containing_eighth_cosets,
    generatedFeasibleContainingOutgoingCoefficientInputs_card]
  rfl

/-- Exactly one genuine transition coset returns from the actual sixth class to containing. -/
theorem generatedFeasibleActualTransition_eighth_containing_card :
    Nat.card (generatedFeasibleActualTransitionCosets generatedFeasiblePhysicalRootPair
      generatedFeasibleContainingNewDestination generatedFeasibleContainingOctadDestination) =
        1 := by
  have h := generatedFeasibleActualTransition_reciprocity generatedFeasiblePhysicalRootPair
    generatedFeasibleContainingOctadDestination generatedFeasibleContainingNewDestination
  rw [generatedFeasibleContainingOctad_actual_A_orbit_card,
    generatedFeasibleContainingEighth_actual_A_orbit_card,
    generatedFeasibleActualTransition_containing_eighth_card] at h
  apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 470060236800)
  exact h.symm.trans (by decide)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
