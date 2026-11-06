/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingZeroInputRecognition

/-! The entire actual coefficient-zero destination fiber has exactly 4,320 input cosets.
Identification of this actual orbit with the established outside orbit remains separate. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem zero_input_exists : Nonempty (generatedFeasibleContainingOutgoingCoefficientInputs 0) := by
  have hn : Nat.card (generatedFeasibleContainingOutgoingCoefficientInputs 0) ≠ 0 := by
    rw [generatedFeasibleContainingOutgoingCoefficientInputs_card]
    decide
  exact (Nat.card_ne_zero.mp hn).1

/-- The actual zero destination is distinct from the source's coordinate-return class. -/
theorem generatedFeasibleContainingZero_class_ne_containing :
    generatedFeasibleSecondaryAClass generatedFeasibleContainingZeroDestination ≠
      generatedFeasibleSecondaryAClass generatedFeasibleContainingOctadDestination := by
  intro he
  obtain ⟨c⟩ := zero_input_exists
  have hn := c.property.1
  rw [generatedFeasibleContaining_transition_residual_eq] at hn
  apply hn.2
  left
  exact (generatedFeasibleContaining_zero_input_recognition c.val c.property).trans he

/-- The zero destination differs from the secondary class by the actual residual input geometry. -/
theorem generatedFeasibleContainingZero_class_ne_secondary :
    generatedFeasibleSecondaryAClass generatedFeasibleContainingZeroDestination ≠
      generatedFeasibleSecondaryAClass
        (generatedFeasibleSecondaryAxis generatedFeasiblePhysicalRootPair) := by
  intro he
  obtain ⟨c⟩ := zero_input_exists
  have hn := c.property.1
  rw [generatedFeasibleContaining_transition_residual_eq] at hn
  apply hn.2
  right
  exact (generatedFeasibleContaining_zero_input_recognition c.val c.property).trans he

/-- The entire actual zero-class transition fiber is the full original coefficient-zero fiber.
The previously classified coordinate returns cannot supply additional inputs. -/
theorem generatedFeasibleActualTransition_containing_zero_cosets :
    generatedFeasibleActualTransitionCosets generatedFeasiblePhysicalRootPair
      generatedFeasibleContainingOctadDestination generatedFeasibleContainingZeroDestination =
        generatedFeasibleContainingOutgoingCoefficientInputs 0 := by
  ext c
  constructor
  · intro hc
    have he : generatedFeasibleTransitionDestination generatedFeasiblePhysicalRootPair
        generatedFeasibleContainingOctadDestination c =
          generatedFeasibleSecondaryAClass generatedFeasibleContainingZeroDestination := hc
    have hn : c ∈ generatedFeasibleContainingNoncoordinateInputCosets := by
      rw [generatedFeasibleContaining_transition_residual_eq]
      refine ⟨Set.mem_univ _, ?_⟩
      rintro (hs | ht)
      · exact generatedFeasibleContainingZero_class_ne_containing (he.symm.trans hs)
      · exact generatedFeasibleContainingZero_class_ne_secondary (he.symm.trans ht)
    exact (generatedFeasibleContaining_zero_noncoordinate_input_iff c hn).mp he
  · exact generatedFeasibleContaining_zero_input_recognition c

/-- Exactly 4,320 actual full transition cosets reach the actual zero destination orbit. -/
theorem generatedFeasibleActualTransition_containing_zero_card :
    Nat.card (generatedFeasibleActualTransitionCosets generatedFeasiblePhysicalRootPair
      generatedFeasibleContainingOctadDestination generatedFeasibleContainingZeroDestination) = 4320 := by
  rw [generatedFeasibleActualTransition_containing_zero_cosets,
    generatedFeasibleContainingOutgoingCoefficientInputs_card]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
