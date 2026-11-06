/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentAssembly
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentP0
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentP12

/-! # Fourth-family coverage with the Fifth partner records discharged

The partner identifications `F0+` and `F12+` of worker `gfifth` (Fifth coset images whose forward
triality images are Fourth images; modules `GeneratedAxisGlobalTwelveFourthIdentP0` and `...P12`)
are proved.  What remains for the coverage of the Fourth family: the forward identifications at
the translated root words of roots `3, 4, 6, 7, 9, 10, 14` and the inverse one at root `14`, the two
Tenth partner records (roots `5, 8`), and the Odd classes of the forward image at root twelve and of
the inverse image at root fifteen.  These remain hypotheses here. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalTwelveFourthIdent
open GeneratedAxisGlobalIdent
set_option autoImplicit false

/-- Fourth-family coverage from the partner-facing identifications, the two Tenth partner records
and the two Odd classes; the Fourth-class and Fifth partner identifications are discharged. -/
theorem generatedAxisGlobalTwelve_fourth_covered_of_partners_fifth
    (h3 : FourthIdentForward (generatedAxisGlobalTwelveFourthRootWords 3))
    (h4 : FourthIdentForward (generatedAxisGlobalTwelveFourthRootWords 4))
    (h6 : FourthIdentForward (generatedAxisGlobalTwelveFourthRootWords 6))
    (h7 : FourthIdentForward (generatedAxisGlobalTwelveFourthRootWords 7))
    (h9 : FourthIdentForward (generatedAxisGlobalTwelveFourthRootWords 9))
    (h10 : FourthIdentForward (generatedAxisGlobalTwelveFourthRootWords 10))
    (h14p : FourthIdentForward (generatedAxisGlobalTwelveFourthRootWords 14))
    (h14n : FourthIdentInverse (generatedAxisGlobalTwelveFourthRootWords 14))
    (p5 : ∃ n : List IdentLetter, (∀ l ∈ n, l ≠ IdentLetter.xi) ∧ ∃ i : Fin 12,
      FourthPartner n (fourthPartnerWord 2) (generatedAxisGlobalTwelveRepresentative i))
    (p8 : ∃ n : List IdentLetter, (∀ l ∈ n, l ≠ IdentLetter.xi) ∧ ∃ i : Fin 12,
      FourthPartner n (fourthPartnerWord 3) (generatedAxisGlobalTwelveRepresentative i))
    (hodd12 : sExtra (rhoLocal (generatedAxisGlobalTwelveFourthRootLocal 12) generatedFourthAxis) ∈
      MulAction.orbit H generatedOddAxis)
    (hodd15 : sExtra⁻¹ (rhoLocal (generatedAxisGlobalTwelveFourthRootLocal 15)
      generatedFourthAxis) ∈ MulAction.orbit H generatedOddAxis) :
    GeneratedAxisGlobalTwelveFamilyCovered 3 :=
  generatedAxisGlobalTwelve_fourth_covered_of_partners h3 h4 h6 h7 h9 h10 h14p h14n
    fourthP0_partner fourthP12_partner p5 p8 hodd12 hodd15

end GeneratedAxisGlobalTwelveFourthIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
