/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthRootsA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthRootsB

/-! # Twelfth-family coverage from the images of the remaining root vectors

Both triality images of the Twelfth root vectors `1 5 9 13 21 23 30 31 33 34 35 37` are bound by
gated identifications (`GeneratedAxisGlobalTwelveTwelfthRootsA`,
`GeneratedAxisGlobalTwelveTwelfthRootsB`).  The reduction below asks for both images at the 25
remaining root vectors only; it assumes no family coverage. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalTwelveTwelfthIdent
open GeneratedAxisGlobalIdent
set_option autoImplicit false

/-- The Twelfth root vectors whose two triality images are not yet bound. -/
def twelfthRemainingRoots : Finset (Fin 38) :=
  {2, 3, 4, 6, 7, 8, 10, 11, 12, 14, 15, 16, 17, 18, 19, 20, 22, 24, 25, 26, 27, 28, 29, 32, 36}

/-- Twelfth-family coverage from both triality images at the remaining root vectors. -/
theorem generatedAxisGlobalTwelve_twelfth_covered_of_remaining
    (h : ∀ k ∈ twelfthRemainingRoots, sExtra (twelfthRootX k) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∧
      sExtra⁻¹ (twelfthRootX k) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative) :
    GeneratedAxisGlobalTwelveFamilyCovered 10 := by
  apply generatedAxisGlobalTwelve_twelfth_covered_of_ident
  intro k hk
  have hk0 : k ≠ 0 := (Finset.mem_erase.mp hk).1
  fin_cases k
  · exact absurd rfl hk0
  · exact twelfthRoot1_bound
  · exact h 2 (by decide)
  · exact h 3 (by decide)
  · exact h 4 (by decide)
  · exact twelfthRoot5_bound
  · exact h 6 (by decide)
  · exact h 7 (by decide)
  · exact h 8 (by decide)
  · exact twelfthRoot9_bound
  · exact h 10 (by decide)
  · exact h 11 (by decide)
  · exact h 12 (by decide)
  · exact twelfthRoot13_bound
  · exact h 14 (by decide)
  · exact h 15 (by decide)
  · exact h 16 (by decide)
  · exact h 17 (by decide)
  · exact h 18 (by decide)
  · exact h 19 (by decide)
  · exact h 20 (by decide)
  · exact twelfthRoot21_bound
  · exact h 22 (by decide)
  · exact twelfthRoot23_bound
  · exact h 24 (by decide)
  · exact h 25 (by decide)
  · exact h 26 (by decide)
  · exact h 27 (by decide)
  · exact h 28 (by decide)
  · exact h 29 (by decide)
  · exact twelfthRoot30_bound
  · exact twelfthRoot31_bound
  · exact h 32 (by decide)
  · exact twelfthRoot33_bound
  · exact twelfthRoot34_bound
  · exact twelfthRoot35_bound
  · exact h 36 (by decide)
  · exact twelfthRoot37_bound

end GeneratedAxisGlobalTwelveTwelfthIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
