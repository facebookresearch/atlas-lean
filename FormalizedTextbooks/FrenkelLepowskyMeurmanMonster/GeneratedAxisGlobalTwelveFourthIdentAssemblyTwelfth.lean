/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentAssemblyPartner
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentR3p

/-! # Fourth-family coverage with the Twelfth identification discharged

With the forward identification at the translated root word of root `3` into the Twelfth family
(`GeneratedAxisGlobalTwelveFourthIdentR3p`), the coverage of the Fourth family reduces to the two
Tenth partner records (`p5`, `p8`) and the Odd classes of the forward image at root twelve and of
the inverse image at root fifteen.  These remain hypotheses here; no family coverage is
assumed. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalTwelveFourthIdent
open GeneratedAxisGlobalIdent
set_option autoImplicit false

/-- Fourth-family coverage from the two Tenth partner records and the two Odd classes. -/
theorem generatedAxisGlobalTwelve_fourth_covered_of_tenth_odd
    (p5 : ∃ n : List IdentLetter, (∀ l ∈ n, l ≠ IdentLetter.xi) ∧ ∃ i : Fin 12,
      FourthPartner n (fourthPartnerWord 2) (generatedAxisGlobalTwelveRepresentative i))
    (p8 : ∃ n : List IdentLetter, (∀ l ∈ n, l ≠ IdentLetter.xi) ∧ ∃ i : Fin 12,
      FourthPartner n (fourthPartnerWord 3) (generatedAxisGlobalTwelveRepresentative i))
    (hodd12 : sExtra (rhoLocal (generatedAxisGlobalTwelveFourthRootLocal 12) generatedFourthAxis) ∈
      MulAction.orbit H generatedOddAxis)
    (hodd15 : sExtra⁻¹ (rhoLocal (generatedAxisGlobalTwelveFourthRootLocal 15)
      generatedFourthAxis) ∈ MulAction.orbit H generatedOddAxis) :
    GeneratedAxisGlobalTwelveFamilyCovered 3 :=
  generatedAxisGlobalTwelve_fourth_covered_of_remaining fourthR3p_forward p5 p8 hodd12 hodd15

end GeneratedAxisGlobalTwelveFourthIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
