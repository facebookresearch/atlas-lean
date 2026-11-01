/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentAssemblyTwelfth
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthBindOdd

/-! # Fourth-family coverage with the Odd classes discharged

The forward image at root twelve and the inverse image at root fifteen lie in the Odd orbit
(`generatedAxisGlobalTwelveFourth_root12_positive_odd`,
`generatedAxisGlobalTwelveFourth_root15_negative_odd`, by reversing the proved Odd-to-Fourth
transports).  The coverage of the Fourth family then reduces to the two Tenth partner records
(`p5`, `p8`), which remain hypotheses here; no family coverage is assumed. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalTwelveFourthIdent
open GeneratedAxisGlobalIdent
set_option autoImplicit false

/-- Fourth-family coverage from the two Tenth partner records. -/
theorem generatedAxisGlobalTwelve_fourth_covered_of_tenth
    (p5 : ∃ n : List IdentLetter, (∀ l ∈ n, l ≠ IdentLetter.xi) ∧ ∃ i : Fin 12,
      FourthPartner n (fourthPartnerWord 2) (generatedAxisGlobalTwelveRepresentative i))
    (p8 : ∃ n : List IdentLetter, (∀ l ∈ n, l ≠ IdentLetter.xi) ∧ ∃ i : Fin 12,
      FourthPartner n (fourthPartnerWord 3) (generatedAxisGlobalTwelveRepresentative i)) :
    GeneratedAxisGlobalTwelveFamilyCovered 3 :=
  generatedAxisGlobalTwelve_fourth_covered_of_tenth_odd p5 p8
    generatedAxisGlobalTwelveFourth_root12_positive_odd
    generatedAxisGlobalTwelveFourth_root15_negative_odd

end GeneratedAxisGlobalTwelveFourthIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
