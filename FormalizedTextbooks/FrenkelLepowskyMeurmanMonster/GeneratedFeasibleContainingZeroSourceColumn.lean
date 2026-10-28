/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingZeroActualTransitionCounts

/-! The complete containing source column of the actual feasible transition table.

Columns are sources and rows are destinations. For the containing source class (Table 3 index
`2`) every one of the 93,150 genuine transition cosets is recognized in one of five actual A
classes. The six established destination classes, in Table 3 positions `0` through `5`, receive
`[0, 63, 63, 4320, 24192, 64512]` inputs, and every other actual A class receives none. The zero
entries are consequences of complete coverage, not table literals.

Position `4` is represented by the actual one-quarter destination class recognized from all
24,192 one-quarter inputs. Its identification with the established odd representative is the
separate theorem `generatedFeasibleContainingSixteen_class_eq_odd`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The six actual A classes in Table 3 positions `0` through `5`. -/
def generatedFeasibleContainingZeroTableClasses : Fin 6 →
    generatedFeasibleLocalOrbitSpace generatedFeasiblePhysicalRootPair :=
  ![generatedFeasibleSecondaryAClass
      (conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 1),
    generatedFeasibleSecondaryAClass
      (generatedFeasibleSecondaryAxis generatedFeasiblePhysicalRootPair),
    generatedFeasibleSecondaryAClass generatedFeasibleContainingOctadDestination,
    generatedFeasibleSecondaryAClass generatedFeasibleOutsideOctadDestination,
    generatedFeasibleSecondaryAClass generatedFeasibleContainingSixteenDestination,
    generatedFeasibleSecondaryAClass generatedFeasibleContainingNewDestination]

private theorem first_anchor : generatedFeasibleContainingAClassFirst
    (generatedFeasibleSecondaryAClass
      (conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 1)) = 8 := by
  have h := generatedFeasibleContainingEstablishedDestinationSource_first 0
  change (griessConwayEncode
      (conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 1)).2.1
        (Sum.inl (0, generatedFeasiblePhysicalRootPair)) = 8 at h
  exact h

private theorem first_secondary : generatedFeasibleContainingAClassFirst
    (generatedFeasibleSecondaryAClass
      (generatedFeasibleSecondaryAxis generatedFeasiblePhysicalRootPair)) = 0 := by
  have h := generatedFeasibleContainingEstablishedDestinationSource_first 1
  change (griessConwayEncode
      (generatedFeasibleSecondaryAxis generatedFeasiblePhysicalRootPair)).2.1
        (Sum.inl (0, generatedFeasiblePhysicalRootPair)) = 0 at h
  exact h

private theorem first_containing : generatedFeasibleContainingAClassFirst
    (generatedFeasibleSecondaryAClass generatedFeasibleContainingOctadDestination) = 1 := by
  have h := generatedFeasibleContainingEstablishedDestinationSource_first 2
  change (griessConwayEncode generatedFeasibleContainingOctadDestination).2.1
      (Sum.inl (0, generatedFeasiblePhysicalRootPair)) = 1 at h
  exact h

private theorem first_outside : generatedFeasibleContainingAClassFirst
    (generatedFeasibleSecondaryAClass generatedFeasibleOutsideOctadDestination) = 0 := by
  have h := generatedFeasibleContainingEstablishedDestinationSource_first 3
  change (griessConwayEncode generatedFeasibleOutsideOctadDestination).2.1
      (Sum.inl (0, generatedFeasiblePhysicalRootPair)) = 0 at h
  exact h

private theorem first_sixteen : generatedFeasibleContainingAClassFirst
    (generatedFeasibleSecondaryAClass generatedFeasibleContainingSixteenDestination) = 1 / 4 :=
  generatedFeasibleContainingSixteenDestination_first_coordinate

private theorem first_new : generatedFeasibleContainingAClassFirst
    (generatedFeasibleSecondaryAClass generatedFeasibleContainingNewDestination) = 1 / 8 :=
  generatedFeasibleContainingNewDestination_first_coordinate

private theorem first_values (k : Fin 6) :
    generatedFeasibleContainingAClassFirst (generatedFeasibleContainingZeroTableClasses k) =
      ![(8 : ℝ), 0, 1, 0, 1 / 4, 1 / 8] k := by
  fin_cases k <;>
    simp [generatedFeasibleContainingZeroTableClasses, first_anchor, first_secondary,
      first_containing, first_outside, first_sixteen, first_new]

/-- The six Table 3 classes are pairwise distinct actual A classes. -/
theorem generatedFeasibleContainingZeroTableClasses_injective :
    Function.Injective generatedFeasibleContainingZeroTableClasses := by
  intro i j he
  have hi := congrArg generatedFeasibleContainingAClassFirst he
  rw [first_values, first_values] at hi
  fin_cases i <;> fin_cases j <;> first | rfl | norm_num at hi
  · exact False.elim (generatedFeasibleContainingZeroOutsideAnchor_class_ne_secondary he.symm)
  · exact False.elim (generatedFeasibleContainingZeroOutsideAnchor_class_ne_secondary he)

/-- The number of genuine containing input cosets whose actual destination is a given A class. -/
def generatedFeasibleContainingZeroColumnEntry
    (X : generatedFeasibleLocalOrbitSpace generatedFeasiblePhysicalRootPair) : ℕ :=
  Nat.card {c : generatedFeasibleTransitionCosetSpace generatedFeasiblePhysicalRootPair |
    generatedFeasibleTransitionDestination generatedFeasiblePhysicalRootPair
      generatedFeasibleContainingOctadDestination c = X}

/-- The column entry of an actual representative is its genuine transition-coset count. -/
theorem generatedFeasibleContainingZeroColumnEntry_class (x : GriessSpace) :
    generatedFeasibleContainingZeroColumnEntry (generatedFeasibleSecondaryAClass x) =
      Nat.card (generatedFeasibleActualTransitionCosets generatedFeasiblePhysicalRootPair
        generatedFeasibleContainingOctadDestination x) := rfl

private theorem table_two : generatedFeasibleContainingZeroTableClasses 2 =
    generatedFeasibleSecondaryAClass generatedFeasibleContainingOctadDestination := by
  simp [generatedFeasibleContainingZeroTableClasses]

private theorem table_one : generatedFeasibleContainingZeroTableClasses 1 =
    generatedFeasibleSecondaryAClass
      (generatedFeasibleSecondaryAxis generatedFeasiblePhysicalRootPair) := by
  simp [generatedFeasibleContainingZeroTableClasses]

private theorem table_three : generatedFeasibleContainingZeroTableClasses 3 =
    generatedFeasibleSecondaryAClass generatedFeasibleOutsideOctadDestination := by
  simp [generatedFeasibleContainingZeroTableClasses]

private theorem table_four : generatedFeasibleContainingZeroTableClasses 4 =
    generatedFeasibleSecondaryAClass generatedFeasibleContainingSixteenDestination := by
  simp [generatedFeasibleContainingZeroTableClasses]

private theorem table_five : generatedFeasibleContainingZeroTableClasses 5 =
    generatedFeasibleSecondaryAClass generatedFeasibleContainingNewDestination := by
  simp [generatedFeasibleContainingZeroTableClasses]

/-- Every genuine containing input coset reaches one of the five realized Table 3 classes
`1` through `5`. -/
theorem generatedFeasibleContainingZeroTable_coverage
    (c : generatedFeasibleTransitionCosetSpace generatedFeasiblePhysicalRootPair) :
    ∃ k : Fin 6, k ≠ 0 ∧
      generatedFeasibleTransitionDestination generatedFeasiblePhysicalRootPair
        generatedFeasibleContainingOctadDestination c =
          generatedFeasibleContainingZeroTableClasses k := by
  obtain ⟨k, hk⟩ := generatedFeasibleContainingActualColumnSources_coverage c
  fin_cases k
  · refine ⟨2, by decide, hk.trans ?_⟩
    rw [table_two]
    simp [generatedFeasibleContainingActualColumnSources]
  · refine ⟨1, by decide, hk.trans ?_⟩
    rw [table_one]
    simp [generatedFeasibleContainingActualColumnSources]
  · refine ⟨3, by decide, hk.trans ?_⟩
    rw [table_three]
    simp [generatedFeasibleContainingActualColumnSources]
  · refine ⟨4, by decide, hk.trans ?_⟩
    rw [table_four]
    simp [generatedFeasibleContainingActualColumnSources]
  · refine ⟨5, by decide, hk.trans ?_⟩
    rw [table_five]
    simp [generatedFeasibleContainingActualColumnSources]

/-- Any actual A class outside the six established Table 3 classes receives no input. -/
theorem generatedFeasibleContainingZeroColumnEntry_other
    (X : generatedFeasibleLocalOrbitSpace generatedFeasiblePhysicalRootPair)
    (hX : ∀ k : Fin 6, X ≠ generatedFeasibleContainingZeroTableClasses k) :
    generatedFeasibleContainingZeroColumnEntry X = 0 := by
  rw [generatedFeasibleContainingZeroColumnEntry, Nat.card_eq_zero]
  left
  constructor
  rintro ⟨c, hc⟩
  obtain ⟨k, _, hk⟩ := generatedFeasibleContainingZeroTable_coverage c
  exact hX k (hc.symm.trans hk)

/-- The singleton opposite-axis class (Table 3 position `0`) receives no containing input. -/
theorem generatedFeasibleContainingZeroColumnEntry_first :
    generatedFeasibleContainingZeroColumnEntry (generatedFeasibleContainingZeroTableClasses 0) =
      0 := by
  rw [generatedFeasibleContainingZeroColumnEntry, Nat.card_eq_zero]
  left
  constructor
  rintro ⟨c, hc⟩
  obtain ⟨k, hk0, hk⟩ := generatedFeasibleContainingZeroTable_coverage c
  exact hk0 (generatedFeasibleContainingZeroTableClasses_injective (hk.symm.trans hc))

/-- The complete actual containing source column in Table 3 positions `0` through `5`. -/
theorem generatedFeasibleContainingZeroColumnEntry_table (k : Fin 6) :
    generatedFeasibleContainingZeroColumnEntry (generatedFeasibleContainingZeroTableClasses k) =
      ![0, 63, 63, 4320, 24192, 64512] k := by
  have h0 := generatedFeasibleContainingZeroColumnEntry_first
  have h1 := generatedFeasibleActualTransition_containing_secondary_card
  have h2 := generatedFeasibleContaining_self_return_cosets_card
  have h3 := generatedFeasibleActualTransition_containing_outside_card
  have h4 := generatedFeasibleActualTransition_containing_sixteen_card
  have h5 := generatedFeasibleActualTransition_containing_eighth_card
  fin_cases k
  · simpa using h0
  · rw [show (⟨1, by decide⟩ : Fin 6) = 1 from rfl, table_one,
      generatedFeasibleContainingZeroColumnEntry_class, h1]
    rfl
  · rw [show (⟨2, by decide⟩ : Fin 6) = 2 from rfl, table_two,
      generatedFeasibleContainingZeroColumnEntry_class, h2]
    rfl
  · rw [show (⟨3, by decide⟩ : Fin 6) = 3 from rfl, table_three,
      generatedFeasibleContainingZeroColumnEntry_class, h3]
    rfl
  · rw [show (⟨4, by decide⟩ : Fin 6) = 4 from rfl, table_four,
      generatedFeasibleContainingZeroColumnEntry_class, h4]
    rfl
  · rw [show (⟨5, by decide⟩ : Fin 6) = 5 from rfl, table_five,
      generatedFeasibleContainingZeroColumnEntry_class, h5]
    rfl

/-- The six entries exhaust all 93,150 genuine containing transition cosets. -/
theorem generatedFeasibleContainingZeroColumnEntry_total :
    ∑ k : Fin 6,
        generatedFeasibleContainingZeroColumnEntry (generatedFeasibleContainingZeroTableClasses k) =
      Nat.card (generatedFeasibleTransitionCosetSpace generatedFeasiblePhysicalRootPair) := by
  rw [generatedFeasibleTransitionCosetSpace_card]
  simp only [generatedFeasibleContainingZeroColumnEntry_table]
  decide

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
