/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhTriangle
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentR7p

/-! # Seventh cell 20 from the Fourth root 7 identification

grecip's gated identification `fourthR7p_ident` sends the translated Fourth root word 7 forward
to the Seventh representative under the word `fourthR7pG` = (Xi-free prefix) ++ (odd letters
`[1, 9, 1]`), and `fourth_root7_bound` binds both triality images of that Fourth root vector.
A Seventh forest-letter word `[2, 0, 3, 2]` carries the cell root of Seventh cell 20 to the root
of the candidate `[1, 9, 1]` (kernel check), so the partner triangle lemma
`seventhCell_both_of_triangle` binds both triality images of the Seventh cell 20 vector. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open GeneratedAxisGlobalIdent GeneratedAxisGlobalTwelveFourthIdent
set_option autoImplicit false

/-- The Xi-free prefix of grecip's target word for Fourth root 7. -/
def seventhR7pPrefix : List IdentLetter :=
  [.qel (qmElt (14983992, false)), .sign 552 0, .mono (0, true), .mono (0, true),
  .mono (1, false), .mono (0, true), .mono (1, false), .mono (0, true), .mono (0, true),
  .mono (0, true), .mono (1, false), .mono (0, true), .mono (0, true), .mono (0, true),
  .mono (1, false), .mono (0, false), .mono (0, false), .mono (1, false), .mono (0, true),
  .mono (1, false), .mono (0, false), .mono (0, false), .mono (1, false), .mono (0, true),
  .mono (1, false), .mono (0, false), .mono (0, false), .mono (1, true), .mono (0, true),
  .mono (0, true), .mono (1, true), .mono (0, true), .mono (1, true), .mono (0, true),
  .mono (0, true), .mono (1, true), .mono (0, true), .mono (1, true), .mono (0, false),
  .mono (1, true), .mono (0, false), .mono (1, true), .mono (0, false), .mono (0, false),
  .mono (1, true), .mono (0, false), .mono (1, true), .mono (0, false), .mono (0, false),
  .mono (1, false), .mono (0, true), .mono (0, true), .mono (1, false), .mono (0, false),
  .mono (1, false), .mono (0, true), .mono (0, true), .mono (1, false), .mono (0, false),
  .mono (1, false), .mono (0, false), .mono (0, false), .mono (1, false), .mono (0, true),
  .mono (0, true), .mono (1, false), .mono (0, true), .mono (0, true), .mono (1, false),
  .mono (0, false)]

/-- grecip's target word is the prefix followed by the candidate odd letters `[1, 9, 1]`. -/
theorem seventhR7p_word :
    fourthR7pG = seventhR7pPrefix ++ ([1, 9, 1] : List (Fin 10)).flatMap sixthOddIdent := rfl

/-- The prefix contains no Xi letter. -/
theorem seventhR7pPrefix_noXi : ∀ l ∈ seventhR7pPrefix, l ≠ IdentLetter.xi := by
  simp [seventhR7pPrefix]

set_option maxRecDepth 100000 in
/-- The forest-letter word `[2, 0, 3, 2]` carries the root of cell 20 to the candidate root. -/
theorem seventhR7p_transport : ([1, 9, 1] : List (Fin 10)).foldr (fun l x =>
    generatedAxisGlobalMaskRowsAction (generatedAxisGlobalOddSourceRows l) x)
      (seventhBitsetWordApply [2, 0, 3, 2] (seventhCellMask 20)) = 2048 := by
  decide +kernel

/-- Both triality images of the Seventh cell 20 vector lie in the twelve local orbits. -/
theorem seventhCell20_both_of_R7p :
    sExtra (rhoLocal (seventhCellWord 20) generatedSeventhAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∧
      sExtra⁻¹ (rhoLocal (seventhCellWord 20) generatedSeventhAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  obtain ⟨hp, hm⟩ := fourth_root7_bound
  have hxeq := fourthSourceWord_apply (generatedAxisGlobalTwelveFourthRootWords 7)
  change sExtra (rhoLocal ((generatedAxisGlobalTwelveFourthRootWords 7).map
      generatedAxisGlobalOddSourceLocalLetter).prod generatedFourthAxis) ∈ _ at hp
  change sExtra⁻¹ (rhoLocal ((generatedAxisGlobalTwelveFourthRootWords 7).map
      generatedAxisGlobalOddSourceLocalLetter).prod generatedFourthAxis) ∈ _ at hm
  rw [hxeq] at hp hm
  refine seventhCell_both_of_triangle 20 [1, 9, 1] (by decide) [2, 0, 3, 2] seventhR7p_transport
    seventhR7pPrefix seventhR7pPrefix_noXi _ ⟨3, _, rfl⟩ hp hm (Or.inl ?_)
  rw [← seventhR7p_word]
  exact fourthR7p_ident

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
