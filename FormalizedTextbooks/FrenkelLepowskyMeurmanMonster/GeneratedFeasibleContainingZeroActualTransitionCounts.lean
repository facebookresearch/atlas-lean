/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingZeroOutsideClassIdentification

/-! Full actual containing-to-outside 4320 and reciprocal outside-to-containing 120 counts.

The genuine containing-to-outside transition fiber is exactly the original coefficient-zero input
fiber; the reverse count follows from actual weighted reciprocity and the two independently counted
actual A orbits. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The entire containing-to-outside fiber is the original complete coefficient-zero input fiber. -/
theorem generatedFeasibleActualTransition_containing_outside_cosets :
    generatedFeasibleActualTransitionCosets generatedFeasiblePhysicalRootPair
      generatedFeasibleContainingOctadDestination generatedFeasibleOutsideOctadDestination =
        generatedFeasibleContainingOutgoingCoefficientInputs 0 := by
  have he : generatedFeasibleActualTransitionCosets generatedFeasiblePhysicalRootPair
      generatedFeasibleContainingOctadDestination generatedFeasibleOutsideOctadDestination =
        generatedFeasibleActualTransitionCosets generatedFeasiblePhysicalRootPair
          generatedFeasibleContainingOctadDestination
            generatedFeasibleContainingZeroDestination := by
    ext c
    change (_ = generatedFeasibleSecondaryAClass generatedFeasibleOutsideOctadDestination) ↔
      (_ = generatedFeasibleSecondaryAClass generatedFeasibleContainingZeroDestination)
    rw [generatedFeasibleContaining_zero_class_eq_outside]
  exact he.trans generatedFeasibleActualTransition_containing_zero_cosets

/-- Exactly 4320 actual transition cosets reach the entire established outside A class. -/
theorem generatedFeasibleActualTransition_containing_outside_card :
    Nat.card (generatedFeasibleActualTransitionCosets generatedFeasiblePhysicalRootPair
      generatedFeasibleContainingOctadDestination generatedFeasibleOutsideOctadDestination) =
        4320 := by
  rw [generatedFeasibleActualTransition_containing_outside_cosets,
    generatedFeasibleContainingOutgoingCoefficientInputs_card]
  rfl

/-- Complete actual reciprocity and independently counted full A orbits give exactly 120 inputs.
-/
theorem generatedFeasibleActualTransition_outside_containing_card :
    Nat.card (generatedFeasibleActualTransitionCosets generatedFeasiblePhysicalRootPair
      generatedFeasibleOutsideOctadDestination generatedFeasibleContainingOctadDestination) =
        120 := by
  have h := generatedFeasibleActualTransition_reciprocity generatedFeasiblePhysicalRootPair
    generatedFeasibleContainingOctadDestination generatedFeasibleOutsideOctadDestination
  rw [generatedFeasibleContainingOctad_actual_A_orbit_card,
    generatedFeasibleOutsideOctad_actual_A_orbit_card,
    generatedFeasibleActualTransition_containing_outside_card] at h
  omega

/-- The five actual A classes reached by the original containing source, with the zero output
replaced by the established outside representative. -/
def generatedFeasibleContainingActualColumnSources : Fin 5 → GriessSpace :=
  ![generatedFeasibleContainingOctadDestination,
    generatedFeasibleSecondaryAxis generatedFeasiblePhysicalRootPair,
    generatedFeasibleOutsideOctadDestination,
    generatedFeasibleContainingSixteenDestination,
    generatedFeasibleContainingNewDestination]

/-- Every class in the complete geometric column is its faithful established representative. -/
theorem generatedFeasibleContainingActualColumnSources_class (k : Fin 5) :
    generatedFeasibleSecondaryAClass (generatedFeasibleContainingActualColumnSources k) =
      generatedFeasibleSecondaryAClass (generatedFeasibleContainingZeroColumnSources k) := by
  fin_cases k <;>
    simp [generatedFeasibleContainingActualColumnSources,
      generatedFeasibleContainingZeroColumnSources,
      generatedFeasibleContaining_zero_class_eq_outside]

/-- The original containing column has complete actual coverage by its five distinct output
classes. -/
theorem generatedFeasibleContainingActualColumnSources_coverage
    (c : generatedFeasibleTransitionCosetSpace generatedFeasiblePhysicalRootPair) :
    ∃ k : Fin 5,
      generatedFeasibleTransitionDestination generatedFeasiblePhysicalRootPair
        generatedFeasibleContainingOctadDestination c =
          generatedFeasibleSecondaryAClass (generatedFeasibleContainingActualColumnSources k) := by
  obtain ⟨k, hk⟩ := generatedFeasibleContainingZeroColumnSources_coverage c
  exact ⟨k, hk.trans (generatedFeasibleContainingActualColumnSources_class k).symm⟩

/-- Every complete actual containing-column entry follows from the original full coset proofs. -/
theorem generatedFeasibleContainingActualColumnSources_input_card (k : Fin 5) :
    Nat.card (generatedFeasibleActualTransitionCosets generatedFeasiblePhysicalRootPair
      generatedFeasibleContainingOctadDestination
        (generatedFeasibleContainingActualColumnSources k)) =
        ![63, 63, 4320, 24192, 64512] k := by
  fin_cases k
  · exact generatedFeasibleContaining_self_return_cosets_card
  · exact generatedFeasibleActualTransition_containing_secondary_card
  · exact generatedFeasibleActualTransition_containing_outside_card
  · exact generatedFeasibleActualTransition_containing_sixteen_card
  · exact generatedFeasibleActualTransition_containing_eighth_card

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
