/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthReduction
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthBindOdd

/-! The remaining obligations for Fourth-family coverage after the two Odd-class bindings.

The forward image at root twelve and the inverse image at root fifteen have the Odd class by
reversal of the proved Odd-to-Fourth transports. Seventeen real vectors remain: the forward
images at the fourteen roots other than eleven and twelve, and the inverse images at roots one,
twelve and fourteen. They are the explicit hypotheses of
`generatedAxisGlobalTwelve_fourth_covered_of_open_odd`; they are not asserted here. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Fourth roots whose forward triality vector remains open after the Odd bindings. -/
def generatedAxisGlobalTwelveFourthOpenPositiveOdd : Finset (Fin 16) :=
  {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 13, 14, 15}

/-- Fourth roots whose inverse triality vector remains open after the Odd bindings. -/
def generatedAxisGlobalTwelveFourthOpenNegativeOdd : Finset (Fin 16) :=
  {1, 12, 14}

/-- The seventeen open Fourth vectors suffice for complete Fourth-family coverage. -/
theorem generatedAxisGlobalTwelve_fourth_covered_of_open_odd
    (hpos : ∀ i ∈ generatedAxisGlobalTwelveFourthOpenPositiveOdd,
      sExtra (rhoLocal (generatedAxisGlobalTwelveFourthRootLocal i) generatedFourthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative)
    (hneg : ∀ i ∈ generatedAxisGlobalTwelveFourthOpenNegativeOdd,
      sExtra⁻¹ (rhoLocal (generatedAxisGlobalTwelveFourthRootLocal i) generatedFourthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative) :
    GeneratedAxisGlobalTwelveFamilyCovered 3 := by
  apply generatedAxisGlobalTwelve_fourth_covered_of_open
  · intro i hi
    by_cases h12 : i = 12
    · subst h12
      exact generatedAxisGlobalTwelveFourth_root12_positive
    · apply hpos i
      revert hi h12
      revert i
      decide
  · intro i hi
    by_cases h15 : i = 15
    · subst h15
      exact generatedAxisGlobalTwelveFourth_root15_negative
    · apply hneg i
      revert hi h15
      revert i
      decide

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
