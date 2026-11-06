/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhTransfer
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSixthPhase

/-! Exact pair bindings among the Sixth and Seventh cells.

An identification equation at a Sixth or Seventh cell whose target word is an Xi-free prefix `M`
followed by the identification word of another Sixth or Seventh cell binds, in addition, the
triality image of that other cell of the sign given by the computed Q-phase of `M` (same sign
reversed when `M` fixes Ω, opposite when it sends Ω to `z Ω`). So one identification binds both
cells of such a pair, also at cells without phase merge. The identifications are hypotheses. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open GeneratedAxisGlobalIdent
set_option backward.isDefEq.respectTransparency false

/-- A Seventh inverse identification landing on a Seventh cell binds that cell. -/
theorem seventhCell_of_seventh_neg (i i' : Fin 23) (M : List IdentLetter)
    (hM : ∀ l ∈ M, SixthPhaseLetter l) (hxi : ∀ l ∈ M, l ≠ IdentLetter.xi)
    (h : SeventhCellIdentNeg i 6 (M ++ seventhCellIdent i')) :
    (qmWord (M.map sixthPhaseData) (2048, false) = (2048, false) →
      sExtra (rhoLocal (seventhCellWord i') generatedSeventhAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative) ∧
    (qmWord (M.map sixthPhaseData) (2048, false) = (2048, true) →
      sExtra⁻¹ (rhoLocal (seventhCellWord i') generatedSeventhAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative) := by
  rw [seventhCellWord_ident]
  exact sixthPhase_of_inverse_identity 6 _ M _ hM hxi _ h

/-- A Seventh positive identification landing on a Seventh cell binds that cell. -/
theorem seventhCell_of_seventh_pos (i i' : Fin 23) (M : List IdentLetter)
    (hM : ∀ l ∈ M, SixthPhaseLetter l) (hxi : ∀ l ∈ M, l ≠ IdentLetter.xi)
    (h : SeventhCellIdentPos i 6 (M ++ seventhCellIdent i')) :
    (qmWord (M.map sixthPhaseData) (2048, false) = (2048, false) →
      sExtra⁻¹ (rhoLocal (seventhCellWord i') generatedSeventhAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative) ∧
    (qmWord (M.map sixthPhaseData) (2048, false) = (2048, true) →
      sExtra (rhoLocal (seventhCellWord i') generatedSeventhAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative) := by
  rw [seventhCellWord_ident]
  exact sixthPhase_of_forward_identity 6 _ M _ hM hxi _ h

/-- A Sixth inverse identification landing on a Seventh cell binds that cell. -/
theorem seventhCell_of_sixth_neg (i : Fin 10) (i' : Fin 23) (M : List IdentLetter)
    (hM : ∀ l ∈ M, SixthPhaseLetter l) (hxi : ∀ l ∈ M, l ≠ IdentLetter.xi)
    (h : SixthCellIdentNeg i 6 (M ++ seventhCellIdent i')) :
    (qmWord (M.map sixthPhaseData) (2048, false) = (2048, false) →
      sExtra (rhoLocal (seventhCellWord i') generatedSeventhAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative) ∧
    (qmWord (M.map sixthPhaseData) (2048, false) = (2048, true) →
      sExtra⁻¹ (rhoLocal (seventhCellWord i') generatedSeventhAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative) := by
  rw [seventhCellWord_ident]
  exact sixthPhase_of_inverse_identity 5 _ M _ hM hxi _ h

/-- A Sixth positive identification landing on a Seventh cell binds that cell. -/
theorem seventhCell_of_sixth_pos (i : Fin 10) (i' : Fin 23) (M : List IdentLetter)
    (hM : ∀ l ∈ M, SixthPhaseLetter l) (hxi : ∀ l ∈ M, l ≠ IdentLetter.xi)
    (h : SixthCellIdentPos i 6 (M ++ seventhCellIdent i')) :
    (qmWord (M.map sixthPhaseData) (2048, false) = (2048, false) →
      sExtra⁻¹ (rhoLocal (seventhCellWord i') generatedSeventhAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative) ∧
    (qmWord (M.map sixthPhaseData) (2048, false) = (2048, true) →
      sExtra (rhoLocal (seventhCellWord i') generatedSeventhAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative) := by
  rw [seventhCellWord_ident]
  exact sixthPhase_of_forward_identity 5 _ M _ hM hxi _ h

/-- A Seventh inverse identification landing on a Sixth cell binds that cell. -/
theorem sixthCell_of_seventh_neg (i : Fin 23) (i' : Fin 10) (M : List IdentLetter)
    (hM : ∀ l ∈ M, SixthPhaseLetter l) (hxi : ∀ l ∈ M, l ≠ IdentLetter.xi)
    (h : SeventhCellIdentNeg i 5 (M ++ sixthCellIdent i')) :
    (qmWord (M.map sixthPhaseData) (2048, false) = (2048, false) →
      sExtra (rhoLocal (sixthCellWord i') generatedSixthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative) ∧
    (qmWord (M.map sixthPhaseData) (2048, false) = (2048, true) →
      sExtra⁻¹ (rhoLocal (sixthCellWord i') generatedSixthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative) := by
  rw [sixthCellWord_ident]
  exact sixthPhase_of_inverse_identity 6 _ M _ hM hxi _ h

/-- A Seventh positive identification landing on a Sixth cell binds that cell. -/
theorem sixthCell_of_seventh_pos (i : Fin 23) (i' : Fin 10) (M : List IdentLetter)
    (hM : ∀ l ∈ M, SixthPhaseLetter l) (hxi : ∀ l ∈ M, l ≠ IdentLetter.xi)
    (h : SeventhCellIdentPos i 5 (M ++ sixthCellIdent i')) :
    (qmWord (M.map sixthPhaseData) (2048, false) = (2048, false) →
      sExtra⁻¹ (rhoLocal (sixthCellWord i') generatedSixthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative) ∧
    (qmWord (M.map sixthPhaseData) (2048, false) = (2048, true) →
      sExtra (rhoLocal (sixthCellWord i') generatedSixthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative) := by
  rw [sixthCellWord_ident]
  exact sixthPhase_of_forward_identity 6 _ M _ hM hxi _ h

/-- A Sixth inverse identification landing on a Sixth cell binds that cell. -/
theorem sixthCell_of_sixth_neg (i i' : Fin 10) (M : List IdentLetter)
    (hM : ∀ l ∈ M, SixthPhaseLetter l) (hxi : ∀ l ∈ M, l ≠ IdentLetter.xi)
    (h : SixthCellIdentNeg i 5 (M ++ sixthCellIdent i')) :
    (qmWord (M.map sixthPhaseData) (2048, false) = (2048, false) →
      sExtra (rhoLocal (sixthCellWord i') generatedSixthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative) ∧
    (qmWord (M.map sixthPhaseData) (2048, false) = (2048, true) →
      sExtra⁻¹ (rhoLocal (sixthCellWord i') generatedSixthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative) := by
  rw [sixthCellWord_ident]
  exact sixthPhase_of_inverse_identity 5 _ M _ hM hxi _ h

/-- A Sixth positive identification landing on a Sixth cell binds that cell. -/
theorem sixthCell_of_sixth_pos (i i' : Fin 10) (M : List IdentLetter)
    (hM : ∀ l ∈ M, SixthPhaseLetter l) (hxi : ∀ l ∈ M, l ≠ IdentLetter.xi)
    (h : SixthCellIdentPos i 5 (M ++ sixthCellIdent i')) :
    (qmWord (M.map sixthPhaseData) (2048, false) = (2048, false) →
      sExtra⁻¹ (rhoLocal (sixthCellWord i') generatedSixthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative) ∧
    (qmWord (M.map sixthPhaseData) (2048, false) = (2048, true) →
      sExtra (rhoLocal (sixthCellWord i') generatedSixthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative) := by
  rw [sixthCellWord_ident]
  exact sixthPhase_of_forward_identity 5 _ M _ hM hxi _ h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
