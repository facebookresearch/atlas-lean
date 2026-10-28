/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhTriangle
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentR10p

/-! # Sixth cell 2 from the Fourth root 10 identification

grecip's gated forward identification `fourthR10p_ident` sends the translated Fourth root word 10
to the Sixth representative under an Xi-free prefix followed by the cell word of Sixth cell `2`, and
`fourth_root10_bound` binds both triality images of the Fourth root 10 vector (root 10 is phase
merged on the Fourth side); the cell triangle lemma binds both images of the Sixth cell 2
vector. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open GeneratedAxisGlobalIdent GeneratedAxisGlobalTwelveFourthIdent
set_option autoImplicit false

/-- The Xi-free prefix of grecip's target word for Fourth root 10. -/
def partnerR10pPrefix : List IdentLetter :=
  [.qel (qmElt (11882499, false)), .sign 1890 0, .mono (1, false), .mono (0, false),
  .mono (0, false), .mono (1, false), .mono (0, true), .mono (1, false), .mono (0, true),
  .mono (0, true), .mono (1, false), .mono (0, false), .mono (0, false), .mono (1, false),
  .mono (0, false), .mono (0, false), .mono (1, false), .mono (0, false), .mono (1, false),
  .mono (0, false), .mono (1, false), .mono (0, true), .mono (0, true), .mono (1, false),
  .mono (0, true), .mono (0, true), .mono (1, false), .mono (0, true), .mono (1, false),
  .mono (0, false), .mono (0, false), .mono (1, true), .mono (0, false), .mono (0, false),
  .mono (1, true), .mono (0, true), .mono (1, true), .mono (0, true), .mono (1, true),
  .mono (0, false), .mono (0, false), .mono (1, true), .mono (0, false), .mono (1, true),
  .mono (0, true), .mono (1, true), .mono (0, true), .mono (1, true), .mono (0, false),
  .mono (0, false), .mono (1, true), .mono (0, false), .mono (0, false), .mono (1, true),
  .mono (0, false), .mono (0, false), .mono (1, false), .mono (0, false), .mono (0, false),
  .mono (0, false), .mono (1, false), .mono (0, false), .mono (0, false), .mono (1, false),
  .mono (0, false), .mono (0, false), .mono (1, false), .mono (0, false), .mono (1, false),
  .mono (0, true), .mono (1, false), .mono (0, false), .mono (1, false), .mono (0, false),
  .mono (1, false), .mono (0, true), .mono (0, true), .mono (1, false)]

/-- grecip's target word for Fourth root 10 ends with the cell word of Sixth cell 2. -/
theorem partnerR10p_word : fourthR10pG = partnerR10pPrefix ++ sixthCellIdent 2 := rfl

/-- Both triality images of the Sixth cell 2 vector lie in the twelve local orbits. -/
theorem sixthCell2_both_of_R10 :
    sExtra (rhoLocal (sixthCellWord 2) generatedSixthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∧
      sExtra⁻¹ (rhoLocal (sixthCellWord 2) generatedSixthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  obtain ⟨hp, hm⟩ := fourth_root10_bound
  have hxeq := fourthSourceWord_apply (generatedAxisGlobalTwelveFourthRootWords 10)
  change sExtra (rhoLocal ((generatedAxisGlobalTwelveFourthRootWords 10).map
      generatedAxisGlobalOddSourceLocalLetter).prod generatedFourthAxis) ∈ _ at hp
  change sExtra⁻¹ (rhoLocal ((generatedAxisGlobalTwelveFourthRootWords 10).map
      generatedAxisGlobalOddSourceLocalLetter).prod generatedFourthAxis) ∈ _ at hm
  rw [hxeq] at hp hm
  exact sixthCell_both_of_cell_triangle 2 partnerR10pPrefix (by simp [partnerR10pPrefix]) _
    ⟨3, _, rfl⟩ hp hm (Or.inl (by rw [← partnerR10p_word]; exact fourthR10p_ident))

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
