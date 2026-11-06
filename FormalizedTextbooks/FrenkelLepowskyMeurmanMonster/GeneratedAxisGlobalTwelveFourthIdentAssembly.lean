/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentF2
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentF13
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentF15
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentF1
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentF12

/-! # Fourth-family coverage with the five Fourth-class identifications discharged

The five whole-vector identifications between local images of the Fourth axis (roots two,
thirteen, fifteen, one and twelve; modules `GeneratedAxisGlobalTwelveFourthIdentF*`) are proved.
What remains for the coverage of the Fourth family: the forward identifications at the translated
root words of roots `3, 4, 6, 7, 9, 10, 14` and the inverse one at root `14` (into the Twelfth,
Root-eight, Seventh, Eighth and Sixth families), the four partner records (roots `0, 1, 5, 8`),
and the Odd classes of the forward image at root twelve and of the inverse image at root
fifteen.  These remain hypotheses here. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalTwelveFourthIdent
open GeneratedAxisGlobalIdent
set_option autoImplicit false

/-- Fourth-family coverage from the partner-facing identifications, the partner records and the
two Odd classes; the Fourth-class identifications are discharged. -/
theorem generatedAxisGlobalTwelve_fourth_covered_of_partners
    (h3 : FourthIdentForward (generatedAxisGlobalTwelveFourthRootWords 3))
    (h4 : FourthIdentForward (generatedAxisGlobalTwelveFourthRootWords 4))
    (h6 : FourthIdentForward (generatedAxisGlobalTwelveFourthRootWords 6))
    (h7 : FourthIdentForward (generatedAxisGlobalTwelveFourthRootWords 7))
    (h9 : FourthIdentForward (generatedAxisGlobalTwelveFourthRootWords 9))
    (h10 : FourthIdentForward (generatedAxisGlobalTwelveFourthRootWords 10))
    (h14p : FourthIdentForward (generatedAxisGlobalTwelveFourthRootWords 14))
    (h14n : FourthIdentInverse (generatedAxisGlobalTwelveFourthRootWords 14))
    (p0 : ∃ n : List IdentLetter, (∀ l ∈ n, l ≠ IdentLetter.xi) ∧ ∃ i : Fin 12,
      FourthPartner n (fourthPartnerWord 0) (generatedAxisGlobalTwelveRepresentative i))
    (p1 : ∃ n : List IdentLetter, (∀ l ∈ n, l ≠ IdentLetter.xi) ∧
      FourthPartner n (fourthPartnerWord 1) (generatedAxisGlobalTwelveRepresentative 4))
    (p5 : ∃ n : List IdentLetter, (∀ l ∈ n, l ≠ IdentLetter.xi) ∧ ∃ i : Fin 12,
      FourthPartner n (fourthPartnerWord 2) (generatedAxisGlobalTwelveRepresentative i))
    (p8 : ∃ n : List IdentLetter, (∀ l ∈ n, l ≠ IdentLetter.xi) ∧ ∃ i : Fin 12,
      FourthPartner n (fourthPartnerWord 3) (generatedAxisGlobalTwelveRepresentative i))
    (hodd12 : sExtra (rhoLocal (generatedAxisGlobalTwelveFourthRootLocal 12) generatedFourthAxis) ∈
      MulAction.orbit H generatedOddAxis)
    (hodd15 : sExtra⁻¹ (rhoLocal (generatedAxisGlobalTwelveFourthRootLocal 15)
      generatedFourthAxis) ∈ MulAction.orbit H generatedOddAxis) :
    GeneratedAxisGlobalTwelveFamilyCovered 3 :=
  generatedAxisGlobalTwelve_fourth_covered_of_idents h3 h4 h6 h7 h9 h10 h14p h14n
    fourthF2_inverse fourthF13_inverse fourthF15_self fourthF1_self fourthF12_self
    p0 p1 p5 p8 hodd12 hodd15

end GeneratedAxisGlobalTwelveFourthIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
