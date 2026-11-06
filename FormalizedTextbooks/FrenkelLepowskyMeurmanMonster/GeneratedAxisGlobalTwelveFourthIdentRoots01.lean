/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentAssemblyFifth

/-! # Fourth roots zero and one

Root zero (phase-merged) is bound by the partner identification `F0+` of worker `gfifth`, and
root one by the Fourth-class identification at its translated pair representative together with
the Fifth-class partner identification `F12+` (the Fourth and Fifth local orbits are disjoint).
Both are now unconditional. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalTwelveFourthIdent
open GeneratedAxisGlobalIdent
set_option autoImplicit false

/-- Root zero of the Fourth forest: both triality images lie in the twelve local orbits. -/
theorem fourth_root0_bound :
    sExtra (rhoLocal (generatedAxisGlobalTwelveFourthRootLocal 0) generatedFourthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∧
      sExtra⁻¹ (rhoLocal (generatedAxisGlobalTwelveFourthRootLocal 0) generatedFourthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  obtain ⟨n, hn, i, q⟩ := fourthP0_partner
  have c := fourthPartner_certificate 0
  exact fourth_partner_merged 0 n hn _ _ c.1 _ c.2 i q

/-- Root one of the Fourth forest: both triality images lie in the twelve local orbits. -/
theorem fourth_root1_bound :
    sExtra (rhoLocal (generatedAxisGlobalTwelveFourthRootLocal 1) generatedFourthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∧
      sExtra⁻¹ (rhoLocal (generatedAxisGlobalTwelveFourthRootLocal 1) generatedFourthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  obtain ⟨n, hn, q⟩ := fourthP12_partner
  have c := fourthPartner_certificate 1
  exact generatedAxisGlobalTwelveFourth_root1_of_classes
    (fourth_root1_fourth_of_ident fourthF1_self) (fourth_partner_orbit 1 n hn _ _ c.1 _ c.2 _ q)

end GeneratedAxisGlobalTwelveFourthIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
