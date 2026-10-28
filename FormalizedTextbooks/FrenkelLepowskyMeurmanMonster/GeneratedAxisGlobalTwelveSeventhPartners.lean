/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhTriangle
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhPairs
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentR14p
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentR14n
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadE26p
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadE26n
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadE9p
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGforestS7c14p
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGforestS7c18p
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGforestS7c12p
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE3x

/-! # Seventh and Sixth cells from gated partner identifications

Partner identifications (grecip, the factory, gident; all gated) whose target words are an
Xi-free prefix followed by an explicit cell word, or whose source words are explicit cell words,
bind cells of the Seventh and Sixth forests:
* Fourth root 14 (grecip `fourthR14p_ident`, `fourthR14n_ident`): both images of the Fourth root
  vector are known, so the cell triangle lemmas bind both images of Seventh cell 21 and of Sixth
  cell 8;
* Eighth root 37 (factory, goctad records E26+, E26-): both images of the Eighth root vector,
  hence both images of Seventh cells 22 and 1;
* Eighth root 13 (factory, goctad record E9+): one image of Seventh cell 8 by the Q-phase lemma,
  hence both (cell 8 is phase merged);
* the factory's identifications at the gforest records S7c14+, S7c18+, S7c12+ (source words are the
  cell words): the positive images of Seventh cells 14, 18, 12;
* Eighth root 6 (gident, goctad record E3+): one image of Sixth cell 5 by the Q-phase lemma, hence
  both (cell 5 is phase merged). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open GeneratedAxisGlobalIdent GeneratedAxisGlobalTwelveFourthIdent
set_option autoImplicit false

/-! ## Fourth root 14: Seventh cell 21 and Sixth cell 8 -/

/-- The Xi-free prefix of grecip's forward target word for Fourth root 14. -/
def partnerR14pPrefix : List IdentLetter :=
  [.qel (qmElt (11923762, false)), .sign 1276 0, .mono (0, false), .mono (0, false),
  .mono (1, false), .mono (0, false), .mono (1, false), .mono (0, false), .mono (1, false),
  .mono (0, true), .mono (1, false), .mono (0, false), .mono (0, false), .mono (0, false),
  .mono (1, false), .mono (0, false), .mono (1, false), .mono (0, false), .mono (0, false),
  .mono (1, false), .mono (0, false), .mono (1, false), .mono (0, true), .mono (0, true),
  .mono (0, true), .mono (1, true), .mono (0, false), .mono (1, true), .mono (0, false),
  .mono (1, true), .mono (0, false), .mono (0, false), .mono (1, true), .mono (0, false),
  .mono (0, false), .mono (1, true), .mono (0, true), .mono (0, true), .mono (0, true),
  .mono (1, true), .mono (0, false), .mono (0, false), .mono (0, false), .mono (1, true),
  .mono (0, true), .mono (1, true), .mono (0, false), .mono (0, false), .mono (0, false),
  .mono (0, false), .mono (1, false), .mono (0, false), .mono (1, false), .mono (0, false),
  .mono (1, false), .mono (0, true), .mono (1, false), .mono (0, false), .mono (1, false),
  .mono (0, false), .mono (1, false), .mono (0, true), .mono (0, true), .mono (0, true),
  .mono (1, false), .mono (0, true), .mono (0, true), .mono (1, false), .mono (0, true),
  .mono (0, true), .mono (0, true), .mono (1, false)]

/-- The Xi-free prefix of grecip's inverse target word for Fourth root 14. -/
def partnerR14nPrefix : List IdentLetter :=
  [.qel (qmElt (766944, false)), .sign 926 0, .mono (0, true), .mono (0, true), .mono (1, false),
  .mono (0, true), .mono (1, false), .mono (0, true), .mono (1, false), .mono (0, false),
  .mono (0, false), .mono (1, false), .mono (0, false), .mono (0, false), .mono (1, false),
  .mono (0, true), .mono (1, false), .mono (0, true), .mono (0, true), .mono (1, false),
  .mono (0, true), .mono (1, false), .mono (0, false), .mono (1, false), .mono (0, true),
  .mono (0, true), .mono (1, true), .mono (0, false), .mono (1, true), .mono (0, false),
  .mono (0, false), .mono (0, false), .mono (1, true), .mono (0, true), .mono (0, true),
  .mono (1, true), .mono (0, false), .mono (0, false), .mono (1, true), .mono (0, false),
  .mono (0, false), .mono (1, true), .mono (0, true), .mono (1, true), .mono (0, false),
  .mono (1, false), .mono (0, false), .mono (1, false), .mono (0, true), .mono (0, true),
  .mono (1, false), .mono (0, false), .mono (0, false), .mono (1, false), .mono (0, false),
  .mono (1, false), .mono (0, true), .mono (0, true), .mono (0, true), .mono (1, false),
  .mono (0, false), .mono (0, false), .mono (0, false), .mono (1, false), .mono (0, false),
  .mono (1, false), .mono (0, false), .mono (0, false), .mono (0, false)]

/-- grecip's forward target word for Fourth root 14 ends with the cell word of Seventh cell 21. -/
theorem partnerR14p_word : fourthR14pG = partnerR14pPrefix ++ seventhCellIdent 21 := rfl

/-- grecip's inverse target word for Fourth root 14 ends with the cell word of Sixth cell 8. -/
theorem partnerR14n_word : fourthR14nG = partnerR14nPrefix ++ sixthCellIdent 8 := rfl

/-- Both triality images of the Fourth root 14 vector lie in the twelve local orbits. -/
theorem partnerR14_vertex :
    rhoLocal (identWordLocal fourthR14pH) (generatedAxisGlobalTwelveRepresentative 3) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∧
      sExtra (rhoLocal (identWordLocal fourthR14pH) (generatedAxisGlobalTwelveRepresentative 3)) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∧
      sExtra⁻¹ (rhoLocal (identWordLocal fourthR14pH)
        (generatedAxisGlobalTwelveRepresentative 3)) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  refine ⟨⟨3, _, rfl⟩, ?_, ?_⟩
  · rw [fourthR14p_ident]
    exact ⟨6, _, rfl⟩
  · change sExtra.symm (rhoLocal (identWordLocal fourthR14nH)
      (generatedAxisGlobalTwelveRepresentative 3)) ∈ _
    rw [fourthR14n_ident]
    exact ⟨5, _, rfl⟩

/-- Both triality images of the Seventh cell 21 vector lie in the twelve local orbits. -/
theorem seventhCell21_both_of_R14 :
    sExtra (rhoLocal (seventhCellWord 21) generatedSeventhAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∧
      sExtra⁻¹ (rhoLocal (seventhCellWord 21) generatedSeventhAxis) ∈
          generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  seventhCell_both_of_cell_triangle 21 partnerR14pPrefix (by simp [partnerR14pPrefix]) _
    partnerR14_vertex.1 partnerR14_vertex.2.1 partnerR14_vertex.2.2
    (Or.inl (by rw [← partnerR14p_word]; exact fourthR14p_ident))

/-- Both triality images of the Sixth cell 8 vector lie in the twelve local orbits. -/
theorem sixthCell8_both_of_R14 :
    sExtra (rhoLocal (sixthCellWord 8) generatedSixthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∧
      sExtra⁻¹ (rhoLocal (sixthCellWord 8) generatedSixthAxis) ∈
          generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  sixthCell_both_of_cell_triangle 8 partnerR14nPrefix (by simp [partnerR14nPrefix]) _
    partnerR14_vertex.1 partnerR14_vertex.2.1 partnerR14_vertex.2.2
    (Or.inr (by rw [← partnerR14n_word]; exact fourthR14n_ident))

/-! ## Eighth root 37: Seventh cells 22 and 1 -/

/-- The Xi-free prefix of the forward target word for Eighth root 37 (record E26+). -/
def partnerE26pPrefix : List IdentLetter :=
  [.qel (qmElt (14272520, true)), .sign 288 0, .mono (0, false), .mono (1, false),
  .mono (0, false), .mono (1, false), .mono (0, false), .mono (0, false), .mono (1, false),
  .mono (0, true), .mono (0, true), .mono (1, false), .mono (0, true), .mono (1, false),
  .mono (0, true), .mono (1, false), .mono (0, false), .mono (1, false), .mono (0, true),
  .mono (0, true), .mono (0, true), .mono (1, false), .mono (0, true), .mono (0, true),
  .mono (0, true), .mono (1, false), .mono (0, true), .mono (0, true), .mono (1, true),
  .mono (0, true), .mono (0, true), .mono (1, true), .mono (0, false), .mono (0, false),
  .mono (1, true), .mono (0, false), .mono (0, false), .mono (0, false), .mono (1, true),
  .mono (0, true), .mono (0, true), .mono (0, true), .mono (1, true), .mono (0, false),
  .mono (1, true), .mono (0, true), .mono (0, true), .mono (0, true), .mono (0, true),
  .mono (1, false), .mono (0, true), .mono (1, false), .mono (0, true), .mono (1, false),
  .mono (0, false), .mono (1, false), .mono (0, true), .mono (0, true), .mono (0, true),
  .mono (1, false), .mono (0, false), .mono (1, false), .mono (0, false), .mono (0, false)]

/-- The Xi-free prefix of the inverse target word for Eighth root 37 (record E26-). -/
def partnerE26nPrefix : List IdentLetter :=
  [.qel (qmElt (4076276, false)), .sign 714 0, .mono (0, true), .mono (0, true),
  .mono (1, false), .mono (0, true), .mono (1, false), .mono (0, true), .mono (1, false),
  .mono (0, false), .mono (1, false), .mono (0, true), .mono (1, false), .mono (0, true),
  .mono (0, true), .mono (0, true), .mono (1, false), .mono (0, false), .mono (0, false),
  .mono (0, false), .mono (1, false), .mono (0, true), .mono (0, true), .mono (0, true),
  .mono (1, true), .mono (0, false), .mono (0, false), .mono (1, true), .mono (0, false),
  .mono (0, false), .mono (0, false), .mono (1, true), .mono (0, true), .mono (1, true),
  .mono (0, false), .mono (0, false), .mono (1, true), .mono (0, true), .mono (1, true),
  .mono (0, false), .mono (1, true), .mono (0, false), .mono (0, false), .mono (1, true),
  .mono (0, true), .mono (1, false), .mono (0, true), .mono (0, true), .mono (0, true),
  .mono (1, false), .mono (0, false), .mono (1, false), .mono (0, true), .mono (1, false),
  .mono (0, true), .mono (0, true), .mono (0, true), .mono (1, false), .mono (0, true),
  .mono (1, false), .mono (0, false), .mono (0, false), .mono (0, false), .mono (1, false),
  .mono (0, true), .mono (1, false), .mono (0, false), .mono (0, false), .mono (0, false)]

/-- The forward target word for Eighth root 37 ends with the cell word of Seventh cell 22. -/
theorem partnerE26p_word : wGoctadE26pG = partnerE26pPrefix ++ seventhCellIdent 22 := rfl

/-- The inverse target word for Eighth root 37 ends with the cell word of Seventh cell 1. -/
theorem partnerE26n_word : wGoctadE26nG = partnerE26nPrefix ++ seventhCellIdent 1 := rfl

/-- Both Eighth root 37 identifications start from the same source word. -/
theorem partnerE26_source : wGoctadE26nH = wGoctadE26pH := rfl

/-- Both triality images of the Eighth root 37 vector lie in the twelve local orbits. -/
theorem partnerE26_vertex :
    rhoLocal (identWordLocal wGoctadE26pH) (generatedAxisGlobalTwelveRepresentative 7) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∧
      sExtra (rhoLocal (identWordLocal wGoctadE26pH) (generatedAxisGlobalTwelveRepresentative 7)) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∧
      sExtra⁻¹ (rhoLocal (identWordLocal wGoctadE26pH)
        (generatedAxisGlobalTwelveRepresentative 7)) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  refine ⟨⟨7, _, rfl⟩, ?_, ?_⟩
  · rw [wGoctadE26p_ident]
    exact ⟨6, _, rfl⟩
  · rw [← partnerE26_source]
    change sExtra.symm (rhoLocal (identWordLocal wGoctadE26nH)
      (generatedAxisGlobalTwelveRepresentative 7)) ∈ _
    rw [wGoctadE26n_ident]
    exact ⟨6, _, rfl⟩

/-- Both triality images of the Seventh cell 22 vector lie in the twelve local orbits. -/
theorem seventhCell22_both_of_E26 :
    sExtra (rhoLocal (seventhCellWord 22) generatedSeventhAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∧
      sExtra⁻¹ (rhoLocal (seventhCellWord 22) generatedSeventhAxis) ∈
          generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  seventhCell_both_of_cell_triangle 22 partnerE26pPrefix (by simp [partnerE26pPrefix]) _
    partnerE26_vertex.1 partnerE26_vertex.2.1 partnerE26_vertex.2.2
    (Or.inl (by rw [← partnerE26p_word]; exact wGoctadE26p_ident))

/-- Both triality images of the Seventh cell 1 vector lie in the twelve local orbits. -/
theorem seventhCell1_both_of_E26 :
    sExtra (rhoLocal (seventhCellWord 1) generatedSeventhAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∧
      sExtra⁻¹ (rhoLocal (seventhCellWord 1) generatedSeventhAxis) ∈
          generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  seventhCell_both_of_cell_triangle 1 partnerE26nPrefix (by simp [partnerE26nPrefix]) _
    partnerE26_vertex.1 partnerE26_vertex.2.1 partnerE26_vertex.2.2
    (Or.inr (by rw [← partnerE26n_word, ← partnerE26_source]; exact wGoctadE26n_ident))

/-! ## Eighth root 13: Seventh cell 8 (phase merged) -/

/-- The Xi-free prefix of the forward target word for Eighth root 13 (record E9+). -/
def partnerE9pPrefix : List IdentLetter :=
  [.qel (qmElt (10510004, false)), .sign 243 0, .mono (1, false), .mono (0, false),
  .mono (1, false), .mono (0, false), .mono (0, false), .mono (1, false), .mono (0, true),
  .mono (1, false), .mono (0, true), .mono (0, true), .mono (1, false), .mono (0, false),
  .mono (0, false), .mono (1, false), .mono (0, true), .mono (1, false), .mono (0, true),
  .mono (1, false), .mono (0, false), .mono (1, false), .mono (0, false), .mono (0, false),
  .mono (1, false), .mono (0, false), .mono (1, true), .mono (0, false), .mono (0, false),
  .mono (0, false), .mono (1, true), .mono (0, false), .mono (1, true), .mono (0, true),
  .mono (0, true), .mono (1, true), .mono (0, false), .mono (0, false), .mono (0, false),
  .mono (1, true), .mono (0, true), .mono (0, true), .mono (0, true), .mono (1, true),
  .mono (0, true), .mono (0, true), .mono (0, true), .mono (1, true), .mono (0, false),
  .mono (0, false), .mono (1, false), .mono (0, true), .mono (0, true), .mono (1, false),
  .mono (0, false), .mono (1, false), .mono (0, false), .mono (0, false), .mono (1, false),
  .mono (0, false), .mono (1, false), .mono (0, true), .mono (0, true), .mono (0, true),
  .mono (1, false), .mono (0, false), .mono (0, false), .mono (1, false), .mono (0, true),
  .mono (0, true), .mono (1, false), .mono (0, false), .mono (0, false)]

/-- The forward target word for Eighth root 13 ends with the cell word of Seventh cell 8. -/
theorem partnerE9p_word : wGoctadE9pG = partnerE9pPrefix ++ seventhCellIdent 8 := rfl

set_option maxRecDepth 100000 in
/-- The Q-phase of the prefix flips the central sign. -/
theorem partnerE9pPrefix_phase :
    qmWord (partnerE9pPrefix.map sixthPhaseData) (2048, false) = (2048, true) := by
  decide +kernel

/-- The positive triality image of the Seventh cell 8 vector lies in the twelve local orbits. -/
theorem seventhCell8_pos_of_E9 :
    sExtra (rhoLocal (seventhCellWord 8) generatedSeventhAxis) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  rw [seventhCellWord_ident]
  exact (sixthPhase_of_forward_identity 7 (identWordLocal wGoctadE9pH) partnerE9pPrefix
    (seventhCellIdent 8) (by simp [partnerE9pPrefix, SixthPhaseLetter])
    (by simp [partnerE9pPrefix]) _ (by rw [← partnerE9p_word]; exact wGoctadE9p_ident)).2
    partnerE9pPrefix_phase

/-! ## The factory's identifications at gforest records -/

/-- Record gforest:S7c14+ (factory): the positive image of Seventh cell 14. -/
theorem seventhCell14_pos_of_factory :
    sExtra (rhoLocal (seventhCellWord 14) generatedSeventhAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  seventhCell_pos_of_ident 14 7 wGforestS7c14pG (by
    unfold SeventhCellIdentPos
    rw [show seventhCellIdent 14 = wGforestS7c14pH from rfl]
    exact wGforestS7c14p_ident)

/-- Record gforest:S7c18+ (factory): the positive image of Seventh cell 18. -/
theorem seventhCell18_pos_of_factory :
    sExtra (rhoLocal (seventhCellWord 18) generatedSeventhAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  seventhCell_pos_of_ident 18 3 wGforestS7c18pG (by
    unfold SeventhCellIdentPos
    rw [show seventhCellIdent 18 = wGforestS7c18pH from rfl]
    exact wGforestS7c18p_ident)

/-- Record gforest:S7c12+ (factory): the positive image of Seventh cell 12. -/
theorem seventhCell12_pos_of_factory :
    sExtra (rhoLocal (seventhCellWord 12) generatedSeventhAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  seventhCell_pos_of_ident 12 9 wGforestS7c12pG (by
    unfold SeventhCellIdentPos
    rw [show seventhCellIdent 12 = wGforestS7c12pH from rfl]
    exact wGforestS7c12p_ident)

/-! ## Eighth root 6: Sixth cell 5 (phase merged) -/

/-- The Xi-free prefix of gident's target word for Eighth root 6 (record E3+). -/
def partnerE3xPrefix : List IdentLetter :=
  [.qel (qmElt (6095288, false)), .sign 29 0, .mono (1, false), .mono (0, true),
  .mono (1, false), .mono (0, true), .mono (0, true), .mono (0, true), .mono (1, false),
  .mono (0, false), .mono (1, false), .mono (0, true), .mono (0, true), .mono (1, false),
  .mono (0, false), .mono (0, false), .mono (1, false), .mono (0, false), .mono (1, false),
  .mono (0, false), .mono (1, false), .mono (0, true), .mono (0, true), .mono (1, false),
  .mono (0, true), .mono (1, true), .mono (0, true), .mono (0, true), .mono (1, true),
  .mono (0, false), .mono (1, true), .mono (0, false), .mono (0, false), .mono (0, false),
  .mono (1, true), .mono (0, false), .mono (1, true), .mono (0, true), .mono (0, true),
  .mono (0, true), .mono (1, true), .mono (0, true), .mono (1, true), .mono (0, false),
  .mono (0, false), .mono (1, true), .mono (0, true), .mono (1, false), .mono (0, true),
  .mono (0, true), .mono (0, true), .mono (1, false), .mono (0, true), .mono (1, false),
  .mono (0, false), .mono (0, false), .mono (1, false), .mono (0, false), .mono (1, false),
  .mono (0, true), .mono (0, true), .mono (1, false), .mono (0, true), .mono (0, true),
  .mono (1, false), .mono (0, true), .mono (1, false)]

/-- gident's target word for Eighth root 6 ends with the cell word of Sixth cell 5. -/
theorem partnerE3x_word : e3xW = partnerE3xPrefix ++ sixthCellIdent 5 := rfl

set_option maxRecDepth 100000 in
/-- The Q-phase of the prefix keeps the central sign. -/
theorem partnerE3xPrefix_phase :
    qmWord (partnerE3xPrefix.map sixthPhaseData) (2048, false) = (2048, false) := by
  decide +kernel

/-- The positive triality image of the Sixth cell 5 vector lies in the twelve local orbits. -/
theorem sixthCell5_pos_of_E3x :
    sExtra (rhoLocal (sixthCellWord 5) generatedSixthAxis) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  have hneg : sExtra⁻¹ (rhoLocal (sixthCellWord 5) generatedSixthAxis) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
    rw [sixthCellWord_ident]
    exact (sixthPhase_of_forward_identity 7 (identWordLocal e3H) partnerE3xPrefix
      (sixthCellIdent 5) (by simp [partnerE3xPrefix, SixthPhaseLetter])
      (by simp [partnerE3xPrefix]) _ (by rw [← partnerE3x_word]; exact e3x_ident)).1
      partnerE3xPrefix_phase
  obtain ⟨k, hk⟩ := sixthCell_phase_merge 5 (by decide)
  rw [hk]
  exact generatedLocalOrbitUnion_local _ k hneg

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
