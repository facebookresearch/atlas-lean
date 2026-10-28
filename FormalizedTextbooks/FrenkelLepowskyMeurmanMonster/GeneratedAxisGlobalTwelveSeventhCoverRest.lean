/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC3n
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC3p
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC10p
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC13p
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC18n
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC19p
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC20n
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhPartnerR7
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhPairC1

/-! # Seventh family coverage: the remaining cells

The cell-vector form of the Seventh coverage criterion
(`generatedAxisGlobalTwelve_seventh_covered_of_cells`) with the cells already bound by gated
identifications discharged: positive images of cells `3` (Fifth target), `10`, `13`, `19` and
`20` (the latter from grecip's Fourth root 7 identification through the partner triangle), and
negative images of cells `1`, `3`, `18`, `20` and `22` (cell 22 through the Q-phase of the record
gforest:S7c1-).  The remaining hypotheses are exactly the triality
images of the other open cells.  This is a reduction, not a closure of `FamilyCovered 6`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open GeneratedAxisGlobalIdent
set_option autoImplicit false

/-- Seventh coverage from the triality images of the cells not yet bound by gated
identifications. -/
theorem generatedAxisGlobalTwelve_seventh_covered_of_remaining
    (hpos : ∀ i ∈ seventhCellOpenPositive, i ∉ ({3, 10, 13, 19, 20} : Finset (Fin 23)) →
      sExtra (rhoLocal (seventhCellWord i) generatedSeventhAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative)
    (hneg : ∀ i ∈ seventhCellOpenNegative, i ∉ ({1, 3, 18, 20, 22} : Finset (Fin 23)) →
      sExtra⁻¹ (rhoLocal (seventhCellWord i) generatedSeventhAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative) :
    GeneratedAxisGlobalTwelveFamilyCovered 6 := by
  apply generatedAxisGlobalTwelve_seventh_covered_of_cells
  · intro i hi
    by_cases h : i ∈ ({3, 10, 13, 19, 20} : Finset (Fin 23))
    · simp only [Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with rfl | rfl | rfl | rfl | rfl
      · exact seventhCell_pos_of_ident 3 4 _ s7c3p_cell
      · exact seventhCell_pos_of_ident 10 6 _ s7c10p_cell
      · exact seventhCell_pos_of_ident 13 6 _ s7c13p_cell
      · exact seventhCell_pos_of_ident 19 6 _ s7c19p_cell
      · exact seventhCell20_both_of_R7p.1
    · exact hpos i hi h
  · intro i hi
    by_cases h : i ∈ ({1, 3, 18, 20, 22} : Finset (Fin 23))
    · simp only [Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with rfl | rfl | rfl | rfl | rfl
      · exact seventhCell_neg_of_ident 1 6 _ s7c1n_cell
      · exact seventhCell_neg_of_ident 3 6 _ s7c3n_cell
      · exact seventhCell_neg_of_ident 18 6 _ s7c18n_cell
      · exact seventhCell20_both_of_R7p.2
      · exact seventhCell22_neg_of_C1n
    · exact hneg i hi h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
