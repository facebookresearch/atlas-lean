/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingZeroClassTransitions
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingEighthActualTransitionCounts

/-! Full actual containing transition-column coverage by its five realized output classes.

The one-quarter output is used through its own actual destination class, recognized from all
24,192 original one-quarter inputs. Its identification with the established odd class is a separate
theorem and is not needed for the coverage argument. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

/-- The actual one-quarter destination class differs from the containing source class. -/
theorem generatedFeasibleContainingZeroSixteen_class_ne_containing :
    generatedFeasibleSecondaryAClass generatedFeasibleContainingSixteenDestination ≠
      generatedFeasibleSecondaryAClass generatedFeasibleContainingOctadDestination := by
  intro he
  have h := congrArg generatedFeasibleContainingAClassFirst he
  change (griessConwayEncode generatedFeasibleContainingSixteenDestination).2.1
      (Sum.inl (0, generatedFeasiblePhysicalRootPair)) =
    (griessConwayEncode generatedFeasibleContainingOctadDestination).2.1
      (Sum.inl (0, generatedFeasiblePhysicalRootPair)) at h
  rw [generatedFeasibleContainingSixteenDestination_first_coordinate] at h
  have hc := generatedFeasibleContainingEstablishedDestinationSource_first 2
  change (griessConwayEncode generatedFeasibleContainingOctadDestination).2.1
      (Sum.inl (0, generatedFeasiblePhysicalRootPair)) = 1 at hc
  rw [hc] at h
  norm_num at h

/-- The actual one-quarter destination class differs from the secondary class. -/
theorem generatedFeasibleContainingZeroSixteen_class_ne_secondary :
    generatedFeasibleSecondaryAClass generatedFeasibleContainingSixteenDestination ≠
      generatedFeasibleSecondaryAClass
        (generatedFeasibleSecondaryAxis generatedFeasiblePhysicalRootPair) := by
  intro he
  have h := congrArg generatedFeasibleContainingAClassFirst he
  change (griessConwayEncode generatedFeasibleContainingSixteenDestination).2.1
      (Sum.inl (0, generatedFeasiblePhysicalRootPair)) =
    (griessConwayEncode (generatedFeasibleSecondaryAxis generatedFeasiblePhysicalRootPair)).2.1
      (Sum.inl (0, generatedFeasiblePhysicalRootPair)) at h
  rw [generatedFeasibleContainingSixteenDestination_first_coordinate] at h
  have hc := generatedFeasibleContainingEstablishedDestinationSource_first 1
  change (griessConwayEncode
      (generatedFeasibleSecondaryAxis generatedFeasiblePhysicalRootPair)).2.1
        (Sum.inl (0, generatedFeasiblePhysicalRootPair)) = 0 at hc
  rw [hc] at h
  norm_num at h

/-- The entire actual one-quarter transition fiber is the full original one-quarter input fiber. -/
theorem generatedFeasibleActualTransition_containing_sixteen_cosets :
    generatedFeasibleActualTransitionCosets generatedFeasiblePhysicalRootPair
      generatedFeasibleContainingOctadDestination generatedFeasibleContainingSixteenDestination =
        generatedFeasibleContainingOutgoingCoefficientInputs 2 := by
  ext c
  constructor
  · intro hc
    have he : generatedFeasibleTransitionDestination generatedFeasiblePhysicalRootPair
        generatedFeasibleContainingOctadDestination c =
          generatedFeasibleSecondaryAClass generatedFeasibleContainingSixteenDestination := hc
    have hn : c ∈ generatedFeasibleContainingNoncoordinateInputCosets := by
      rw [generatedFeasibleContaining_transition_residual_eq]
      refine ⟨Set.mem_univ _, ?_⟩
      rintro (hs | ht)
      · exact generatedFeasibleContainingZeroSixteen_class_ne_containing (he.symm.trans hs)
      · exact generatedFeasibleContainingZeroSixteen_class_ne_secondary (he.symm.trans ht)
    exact (generatedFeasibleContaining_sixteen_noncoordinate_input_iff c hn).mp he
  · exact generatedFeasibleContaining_sixteen_input_recognition c

/-- Exactly 24,192 actual transition cosets reach the actual one-quarter destination class. -/
theorem generatedFeasibleActualTransition_containing_sixteen_card :
    Nat.card (generatedFeasibleActualTransitionCosets generatedFeasiblePhysicalRootPair
      generatedFeasibleContainingOctadDestination generatedFeasibleContainingSixteenDestination) =
        24192 := by
  rw [generatedFeasibleActualTransition_containing_sixteen_cosets,
    generatedFeasibleContainingOutgoingCoefficientInputs_card]
  rfl

/-- The five actual output axes: containing, secondary, zero, one-quarter and one-eighth. -/
def generatedFeasibleContainingZeroColumnSources : Fin 5 → GriessSpace :=
  ![generatedFeasibleContainingOctadDestination,
    generatedFeasibleSecondaryAxis generatedFeasiblePhysicalRootPair,
    generatedFeasibleContainingZeroDestination,
    generatedFeasibleContainingSixteenDestination,
    generatedFeasibleContainingNewDestination]

private theorem first_containing : generatedFeasibleContainingAClassFirst
    (generatedFeasibleSecondaryAClass generatedFeasibleContainingOctadDestination) = 1 := by
  have hc := generatedFeasibleContainingEstablishedDestinationSource_first 2
  change (griessConwayEncode generatedFeasibleContainingOctadDestination).2.1
      (Sum.inl (0, generatedFeasiblePhysicalRootPair)) = 1 at hc
  exact hc

private theorem first_secondary : generatedFeasibleContainingAClassFirst
    (generatedFeasibleSecondaryAClass
      (generatedFeasibleSecondaryAxis generatedFeasiblePhysicalRootPair)) = 0 := by
  have hc := generatedFeasibleContainingEstablishedDestinationSource_first 1
  change (griessConwayEncode
      (generatedFeasibleSecondaryAxis generatedFeasiblePhysicalRootPair)).2.1
        (Sum.inl (0, generatedFeasiblePhysicalRootPair)) = 0 at hc
  exact hc

private theorem first_zero : generatedFeasibleContainingAClassFirst
    (generatedFeasibleSecondaryAClass generatedFeasibleContainingZeroDestination) = 0 :=
  generatedFeasibleContainingZeroDestination_first_coordinate

private theorem first_sixteen : generatedFeasibleContainingAClassFirst
    (generatedFeasibleSecondaryAClass generatedFeasibleContainingSixteenDestination) = 1 / 4 :=
  generatedFeasibleContainingSixteenDestination_first_coordinate

private theorem first_new : generatedFeasibleContainingAClassFirst
    (generatedFeasibleSecondaryAClass generatedFeasibleContainingNewDestination) = 1 / 8 :=
  generatedFeasibleContainingNewDestination_first_coordinate

/-- The exact actual first coefficients distinguish all outputs except secondary and zero. -/
theorem generatedFeasibleContainingZeroColumnSources_first (k : Fin 5) :
    generatedFeasibleContainingAClassFirst
      (generatedFeasibleSecondaryAClass (generatedFeasibleContainingZeroColumnSources k)) =
        ![(1 : ℝ), 0, 0, 1 / 4, 1 / 8] k := by
  fin_cases k <;>
    simp [generatedFeasibleContainingZeroColumnSources, first_containing, first_secondary,
      first_zero, first_sixteen, first_new]

/-- All five output classes are distinct under the entire actual first-axis action. -/
theorem generatedFeasibleContainingZeroColumnSources_class_injective :
    Function.Injective (fun k => generatedFeasibleSecondaryAClass
      (generatedFeasibleContainingZeroColumnSources k)) := by
  intro i j he
  have hi := congrArg generatedFeasibleContainingAClassFirst he
  rw [generatedFeasibleContainingZeroColumnSources_first,
    generatedFeasibleContainingZeroColumnSources_first] at hi
  fin_cases i <;> fin_cases j <;> first | rfl | norm_num at hi
  · exact False.elim (generatedFeasibleContainingZero_class_ne_secondary he.symm)
  · exact False.elim (generatedFeasibleContainingZero_class_ne_secondary he)

/-- All five input counts follow from the complete actual geometric transition proofs. -/
theorem generatedFeasibleContainingZeroColumnSources_input_card (k : Fin 5) :
    Nat.card (generatedFeasibleActualTransitionCosets generatedFeasiblePhysicalRootPair
      generatedFeasibleContainingOctadDestination
        (generatedFeasibleContainingZeroColumnSources k)) =
        ![63, 63, 4320, 24192, 64512] k := by
  fin_cases k
  · exact generatedFeasibleContaining_self_return_cosets_card
  · exact generatedFeasibleActualTransition_containing_secondary_card
  · exact generatedFeasibleActualTransition_containing_zero_card
  · exact generatedFeasibleActualTransition_containing_sixteen_card
  · exact generatedFeasibleActualTransition_containing_eighth_card

/-- The genuine containing input coset space. -/
private abbrev Input := generatedFeasibleTransitionCosetSpace generatedFeasiblePhysicalRootPair
/-- The genuine input fiber of one realized output class. -/
private abbrev Fiber (k : Fin 5) :=
  generatedFeasibleActualTransitionCosets generatedFeasiblePhysicalRootPair
    generatedFeasibleContainingOctadDestination (generatedFeasibleContainingZeroColumnSources k)

/-- Every actual input coset reaches one of the five entire realized output classes. There is
no assumed partition: the disjoint actual fibers exhaust the independently counted whole domain. -/
theorem generatedFeasibleContainingZeroColumnSources_coverage
    (c : generatedFeasibleTransitionCosetSpace generatedFeasiblePhysicalRootPair) :
    ∃ k : Fin 5,
      generatedFeasibleTransitionDestination generatedFeasiblePhysicalRootPair
        generatedFeasibleContainingOctadDestination c =
          generatedFeasibleSecondaryAClass (generatedFeasibleContainingZeroColumnSources k) := by
  have hinput : Nat.card Input = 93150 := generatedFeasibleTransitionCosetSpace_card _
  let _ : Finite Input := Nat.finite_of_card_ne_zero (by rw [hinput]; decide)
  let f : (Σ k : Fin 5, Fiber k) → Input := fun x => x.2.val
  have hf : Function.Injective f := by
    rintro ⟨i, a⟩ ⟨j, b⟩ h
    have he : generatedFeasibleSecondaryAClass (generatedFeasibleContainingZeroColumnSources i) =
        generatedFeasibleSecondaryAClass (generatedFeasibleContainingZeroColumnSources j) := by
      have ha := a.property
      have hb := b.property
      change generatedFeasibleTransitionDestination generatedFeasiblePhysicalRootPair
        generatedFeasibleContainingOctadDestination a.val = _ at ha
      change generatedFeasibleTransitionDestination generatedFeasiblePhysicalRootPair
        generatedFeasibleContainingOctadDestination b.val = _ at hb
      change a.val = b.val at h
      rw [h] at ha
      exact ha.symm.trans hb
    have hij := generatedFeasibleContainingZeroColumnSources_class_injective he
    subst j
    exact congrArg (Sigma.mk i) (Subtype.ext h)
  have hcard : Nat.card (Σ k : Fin 5, Fiber k) = Nat.card Input := by
    rw [Nat.card_sigma, hinput]
    change (∑ k : Fin 5, Nat.card (Fiber k)) = 93150
    simp_rw [show ∀ k, Nat.card (Fiber k) = (![63, 63, 4320, 24192, 64512] : Fin 5 → ℕ) k
      from generatedFeasibleContainingZeroColumnSources_input_card]
    decide
  let _ : Fintype Input := Fintype.ofFinite Input
  let _ : Fintype (Σ k : Fin 5, Fiber k) := Fintype.ofFinite _
  have hs : Function.Surjective f :=
    ((Fintype.bijective_iff_injective_and_card f).mpr
      ⟨hf, by simpa only [Nat.card_eq_fintype_card] using hcard⟩).2
  obtain ⟨⟨k, a⟩, ha⟩ := hs c
  refine ⟨k, ?_⟩
  have h := a.property
  change a.val = c at ha
  change generatedFeasibleTransitionDestination generatedFeasiblePhysicalRootPair
    generatedFeasibleContainingOctadDestination a.val = _ at h
  rwa [ha] at h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
