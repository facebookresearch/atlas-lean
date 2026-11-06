/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingSixteenClassStabilizer

/-! Actual whole-class and original input counts for the one-quarter destination. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- Exactly4,196,966,400 original whole vectors form the one-quarter feasible A orbit. -/
theorem generatedFeasibleContainingSixteen_actual_A_orbit_card :
    Nat.card (MulAction.orbit (localAxisStabilizer generatedFeasiblePhysicalRootPair)
      generatedFeasibleContainingSixteenDestination) = 4196966400 := by
  have h := generatedFeasibleContainingSixteenDestinationStabilizer_index
  rw [generatedFeasibleContainingSixteenDestinationStabilizer, MulAction.index_stabilizer,
    ← Nat.card_coe_set_eq] at h
  exact h

/-- The entire actual containing-to-odd transition fiber is exactly the original one-quarter inputs. -/
theorem generatedFeasibleContainingSixteen_odd_transition_cosets_eq :
    generatedFeasibleActualTransitionCosets generatedFeasiblePhysicalRootPair
      generatedFeasibleContainingOctadDestination generatedFeasibleSecondaryOddDestination =
        generatedFeasibleContainingOutgoingCoefficientInputs 2 := by
  ext c
  induction c using Quotient.inductionOn with
  | h h =>
    constructor
    · intro hc
      change generatedFeasibleSecondaryAClass
        (sExtra (rhoLocal h.val generatedFeasibleContainingOctadDestination)) =
          generatedFeasibleSecondaryAClass generatedFeasibleSecondaryOddDestination at hc
      have hq := congrArg generatedFeasibleContainingAClassFirst hc
      change (griessConwayEncode (sExtra
        (rhoLocal h.val generatedFeasibleContainingOctadDestination))).2.1
          (Sum.inl (0, generatedFeasiblePhysicalRootPair)) =
            (griessConwayEncode generatedFeasibleSecondaryOddDestination).2.1
              (Sum.inl (0, generatedFeasiblePhysicalRootPair)) at hq
      have ho : (griessConwayEncode generatedFeasibleSecondaryOddDestination).2.1
          (Sum.inl (0, generatedFeasiblePhysicalRootPair)) = 1 / 4 :=
        generatedFeasibleContainingEstablishedDestinationSource_first 4
      rw [ho] at hq
      exact (generatedFeasibleContainingOutgoingCoefficientInputs_word_iff h 2).mpr
        (generatedFeasibleSixteen_quarter_input h hq)
    · intro hc
      have hd := generatedFeasibleContaining_sixteen_input_recognition _ hc
      rw [generatedFeasibleContainingSixteen_class_eq_odd] at hd
      exact hd

/-- Exactly24,192 complete original input cosets take the containing class to the odd class. -/
theorem generatedFeasibleActualTransition_containing_odd_card :
    Nat.card (generatedFeasibleActualTransitionCosets generatedFeasiblePhysicalRootPair
      generatedFeasibleContainingOctadDestination generatedFeasibleSecondaryOddDestination) =
        24192 := by
  rw [generatedFeasibleContainingSixteen_odd_transition_cosets_eq]
  exact generatedFeasibleContainingOutgoingCoefficientInputs_card 2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
