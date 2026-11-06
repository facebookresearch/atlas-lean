/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhCells
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSixthIdent

/-! The open Seventh cells in the identification alphabet.

The explicit Seventh cell words are products of the odd source letters `0, 1, 6, 7, 8, 9`, hence
local elements of identification words. The actual Seventh family coverage therefore follows
from identification equations
`sExtra^{±1} (rhoLocal (identWordLocal (seventhCellIdent i)) v₆) = rhoLocal (identWordLocal g) v_j`
at the open cells, where `v_j` are the catalogue representatives; at the phase-merged cells an
equation of either sign suffices. The equations are hypotheses here, not asserted. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open GeneratedAxisGlobalIdent
set_option backward.isDefEq.respectTransparency false

/-- The identification words of the explicit Seventh cell words. -/
def seventhCellIdent (i : Fin 23) : List IdentLetter :=
  (seventhCellLetters i).flatMap sixthOddIdent

/-- Each explicit Seventh cell word is the local element of its identification word. -/
theorem seventhCellWord_ident (i : Fin 23) :
    seventhCellWord i = identWordLocal (seventhCellIdent i) :=
  sixthOddIdent_word _ (by fin_cases i <;> decide)

/-- A positive identification equation at the Seventh cell `i`. -/
def SeventhCellIdentPos (i : Fin 23) (j : Fin 12) (g : List IdentLetter) : Prop :=
  sExtra (rhoLocal (identWordLocal (seventhCellIdent i))
      (generatedAxisGlobalTwelveRepresentative 6)) =
    rhoLocal (identWordLocal g) (generatedAxisGlobalTwelveRepresentative j)

/-- An inverse identification equation at the Seventh cell `i`. -/
def SeventhCellIdentNeg (i : Fin 23) (j : Fin 12) (g : List IdentLetter) : Prop :=
  sExtra⁻¹ (rhoLocal (identWordLocal (seventhCellIdent i))
      (generatedAxisGlobalTwelveRepresentative 6)) =
    rhoLocal (identWordLocal g) (generatedAxisGlobalTwelveRepresentative j)

/-- A positive identification equation binds the positive vector of a Seventh cell. -/
theorem seventhCell_pos_of_ident (i : Fin 23) (j : Fin 12) (g : List IdentLetter)
    (h : SeventhCellIdentPos i j g) :
    sExtra (rhoLocal (seventhCellWord i) generatedSeventhAxis) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  rw [seventhCellWord_ident]
  exact generatedAxisGlobalTwelve_mem_of_transport j _ h

/-- An inverse identification equation binds the inverse vector of a Seventh cell. -/
theorem seventhCell_neg_of_ident (i : Fin 23) (j : Fin 12) (g : List IdentLetter)
    (h : SeventhCellIdentNeg i j g) :
    sExtra⁻¹ (rhoLocal (seventhCellWord i) generatedSeventhAxis) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  rw [seventhCellWord_ident]
  exact generatedAxisGlobalTwelve_mem_of_transport j _ h

/-- At a phase-merged Seventh cell an inverse identification equation binds the positive
vector. -/
theorem seventhCell_pos_of_neg_ident (i : Fin 23)
    (hi : i ∈ ({4, 5, 6, 7, 8, 9, 13, 14, 15, 16, 19} : Finset (Fin 23))) (j : Fin 12)
    (g : List IdentLetter) (h : SeventhCellIdentNeg i j g) :
    sExtra (rhoLocal (seventhCellWord i) generatedSeventhAxis) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  obtain ⟨k, hk⟩ := seventhCell_phase_merge i hi
  rw [hk]
  exact generatedLocalOrbitUnion_local _ k (seventhCell_neg_of_ident i j g h)

/-- Actual Seventh family coverage from identification equations: at each open cell a positive
equation, or at a phase-merged cell an inverse one, and an inverse equation at the cells
`1, 2, 3, 10, 11, 12, 17, 18, 20, 21, 22`. -/
theorem generatedAxisGlobalTwelve_seventh_covered_of_ident
    (hpos : ∀ i ∈ seventhCellOpenPositive,
      (∃ (j : Fin 12) (g : List IdentLetter), SeventhCellIdentPos i j g) ∨
        (i ∈ ({4, 5, 6, 7, 8, 9, 13, 14, 15, 16, 19} : Finset (Fin 23)) ∧
          ∃ (j : Fin 12) (g : List IdentLetter), SeventhCellIdentNeg i j g))
    (hneg : ∀ i ∈ seventhCellOpenNegative,
      ∃ (j : Fin 12) (g : List IdentLetter), SeventhCellIdentNeg i j g) :
    GeneratedAxisGlobalTwelveFamilyCovered 6 := by
  apply generatedAxisGlobalTwelve_seventh_covered_of_cells
  · intro i hi
    rcases hpos i hi with ⟨j, g, h⟩ | ⟨hm, j, g, h⟩
    · exact seventhCell_pos_of_ident i j g h
    · exact seventhCell_pos_of_neg_ident i hm j g h
  · intro i hi
    obtain ⟨j, g, h⟩ := hneg i hi
    exact seventhCell_neg_of_ident i j g h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
