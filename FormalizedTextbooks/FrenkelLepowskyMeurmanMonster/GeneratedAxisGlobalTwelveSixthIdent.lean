/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSixthCells
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentLetters

/-! The open Sixth cells in the identification alphabet.

The explicit Sixth cell words are products of the odd source letters `0, 1, 6, 7, 8, 9`, hence
local elements of words in the identification alphabet `GeneratedAxisGlobalIdent.IdentLetter`
(the inverse source Xi is the square of Xi, since Xi has order three). The actual Sixth family
coverage therefore follows from identification equations
`sExtra^{±1} (rhoLocal (identWordLocal (sixthCellIdent i)) v₅) = rhoLocal (identWordLocal g) v_j`
at the open cells, where `v_j` are the catalogue representatives; at the phase-merged cells an
equation of either sign suffices. The equations are hypotheses here, not asserted. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open GeneratedAxisGlobalIdent
set_option backward.isDefEq.respectTransparency false

/-- The identification word of an odd source letter; the sign letters `2`–`5`, which occur in no
cell word, are sent to the empty word. -/
def sixthOddIdent : Fin 10 → List IdentLetter :=
  ![[.xi], [.xi, .xi], [], [], [], [], [.mono (0, false)], [.mono (0, true)],
    [.mono (1, false)], [.mono (1, true)]]

private theorem sixthOddIdent_xi_inv :
    (localFiberIntoH xiSpinLocalFiber)⁻¹ =
      localFiberIntoH (xiSpinLocalFiber * xiSpinLocalFiber) := by
  have h : xiSpinLocalFiber⁻¹ = xiSpinLocalFiber * xiSpinLocalFiber := by
    apply inv_eq_of_mul_eq_one_right
    simpa only [pow_succ, pow_zero, one_mul, mul_assoc] using xiSpinLocalFiber_cube
  rw [← h, map_inv]

private theorem sixthOddIdent1 :
    identWordLocal [IdentLetter.xi, IdentLetter.xi] =
      generatedAxisGlobalOddSourceLocalLetter 1 := by
  have h : identWordLocal [IdentLetter.xi, IdentLetter.xi] =
      localFiberIntoH (xiSpinLocalFiber * xiSpinLocalFiber) := by
    simp [identWordLocal, identWordFiber, IdentLetter.fiber]
  rw [h, ← sixthOddIdent_xi_inv]
  rfl

private theorem sixthOddIdent0 :
    identWordLocal [IdentLetter.xi] = generatedAxisGlobalOddSourceLocalLetter 0 :=
  identWordLocal_singleton _

private theorem sixthOddIdent6 :
    identWordLocal [IdentLetter.mono (0, false)] = generatedAxisGlobalOddSourceLocalLetter 6 := by
  rw [identWordLocal_singleton]
  rfl

private theorem sixthOddIdent7 :
    identWordLocal [IdentLetter.mono (0, true)] = generatedAxisGlobalOddSourceLocalLetter 7 := by
  rw [identWordLocal_singleton]
  exact map_inv localFiberIntoH _

private theorem sixthOddIdent8 :
    identWordLocal [IdentLetter.mono (1, false)] = generatedAxisGlobalOddSourceLocalLetter 8 := by
  rw [identWordLocal_singleton]
  rfl

private theorem sixthOddIdent9 :
    identWordLocal [IdentLetter.mono (1, true)] = generatedAxisGlobalOddSourceLocalLetter 9 := by
  rw [identWordLocal_singleton]
  exact map_inv localFiberIntoH _

/-- Each odd source letter `0, 1, 6, 7, 8, 9` is the local element of its identification word. -/
theorem sixthOddIdent_local (l : Fin 10) (hl : l.val < 2 ∨ 6 ≤ l.val) :
    identWordLocal (sixthOddIdent l) = generatedAxisGlobalOddSourceLocalLetter l := by
  fin_cases l
  · exact sixthOddIdent0
  · exact sixthOddIdent1
  · exact absurd hl (by decide)
  · exact absurd hl (by decide)
  · exact absurd hl (by decide)
  · exact absurd hl (by decide)
  · exact sixthOddIdent6
  · exact sixthOddIdent7
  · exact sixthOddIdent8
  · exact sixthOddIdent9

/-- A product of the odd source letters `0, 1, 6, 7, 8, 9` is an identification word. -/
theorem sixthOddIdent_word (ls : List (Fin 10)) (hls : ∀ l ∈ ls, l.val < 2 ∨ 6 ≤ l.val) :
    (ls.map generatedAxisGlobalOddSourceLocalLetter).prod =
      identWordLocal (ls.flatMap sixthOddIdent) := by
  induction ls with
  | nil => simp [identWordLocal, identWordFiber]
  | cons l ls ih =>
    rw [List.map_cons, List.prod_cons, List.flatMap_cons, identWordLocal_append,
      sixthOddIdent_local l (hls l (List.mem_cons_self ..)),
      ih (fun m hm => hls m (List.mem_cons_of_mem _ hm))]

/-- The identification words of the explicit Sixth cell words. -/
def sixthCellIdent (i : Fin 10) : List IdentLetter :=
  (sixthCellLetters i).flatMap sixthOddIdent

/-- Each explicit Sixth cell word is the local element of its identification word. -/
theorem sixthCellWord_ident (i : Fin 10) :
    sixthCellWord i = identWordLocal (sixthCellIdent i) :=
  sixthOddIdent_word _ (by fin_cases i <;> decide)

/-- A positive identification equation at the Sixth cell `i`. -/
def SixthCellIdentPos (i : Fin 10) (j : Fin 12) (g : List IdentLetter) : Prop :=
  sExtra (rhoLocal (identWordLocal (sixthCellIdent i))
      (generatedAxisGlobalTwelveRepresentative 5)) =
    rhoLocal (identWordLocal g) (generatedAxisGlobalTwelveRepresentative j)

/-- An inverse identification equation at the Sixth cell `i`. -/
def SixthCellIdentNeg (i : Fin 10) (j : Fin 12) (g : List IdentLetter) : Prop :=
  sExtra⁻¹ (rhoLocal (identWordLocal (sixthCellIdent i))
      (generatedAxisGlobalTwelveRepresentative 5)) =
    rhoLocal (identWordLocal g) (generatedAxisGlobalTwelveRepresentative j)

/-- A positive identification equation binds the positive vector of a Sixth cell. -/
theorem sixthCell_pos_of_ident (i : Fin 10) (j : Fin 12) (g : List IdentLetter)
    (h : SixthCellIdentPos i j g) :
    sExtra (rhoLocal (sixthCellWord i) generatedSixthAxis) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  rw [sixthCellWord_ident]
  exact generatedAxisGlobalTwelve_mem_of_transport j _ h

/-- An inverse identification equation binds the inverse vector of a Sixth cell. -/
theorem sixthCell_neg_of_ident (i : Fin 10) (j : Fin 12) (g : List IdentLetter)
    (h : SixthCellIdentNeg i j g) :
    sExtra⁻¹ (rhoLocal (sixthCellWord i) generatedSixthAxis) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  rw [sixthCellWord_ident]
  exact generatedAxisGlobalTwelve_mem_of_transport j _ h

/-- At a phase-merged Sixth cell an inverse identification equation binds the positive vector. -/
theorem sixthCell_pos_of_neg_ident (i : Fin 10)
    (hi : i ∈ ({3, 4, 5, 6, 7, 9} : Finset (Fin 10))) (j : Fin 12) (g : List IdentLetter)
    (h : SixthCellIdentNeg i j g) :
    sExtra (rhoLocal (sixthCellWord i) generatedSixthAxis) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  obtain ⟨k, hk⟩ := sixthCell_phase_merge i hi
  rw [hk]
  exact generatedLocalOrbitUnion_local _ k (sixthCell_neg_of_ident i j g h)

/-- Actual Sixth family coverage from identification equations: at each open cell a positive
equation, or at a phase-merged cell an inverse one, and an inverse equation at the cells
`1, 2, 8`. -/
theorem generatedAxisGlobalTwelve_sixth_covered_of_ident
    (hpos : ∀ i ∈ sixthCellOpenPositive,
      (∃ (j : Fin 12) (g : List IdentLetter), SixthCellIdentPos i j g) ∨
        (i ∈ ({3, 4, 5, 6, 7, 9} : Finset (Fin 10)) ∧
          ∃ (j : Fin 12) (g : List IdentLetter), SixthCellIdentNeg i j g))
    (hneg : ∀ i ∈ sixthCellOpenNegative,
      ∃ (j : Fin 12) (g : List IdentLetter), SixthCellIdentNeg i j g) :
    GeneratedAxisGlobalTwelveFamilyCovered 5 := by
  apply generatedAxisGlobalTwelve_sixth_covered_of_cells
  · intro i hi
    rcases hpos i hi with ⟨j, g, h⟩ | ⟨hm, j, g, h⟩
    · exact sixthCell_pos_of_ident i j g h
    · exact sixthCell_pos_of_neg_ident i hm j g h
  · intro i hi
    obtain ⟨j, g, h⟩ := hneg i hi
    exact sixthCell_neg_of_ident i j g h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
