/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthActual
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthPhase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthBindRoot11

/-! The remaining obligations for complete triality coverage of the actual Fourth family.

The checked Fourth forest reduces all Fourth transitions to sixteen root words and both
triality signs. Eleven genuine phase merges, the literal octad-image class of the inverse
image at the empty root word, and the octad-side phase merge for its forward image leave
nineteen real vectors: the forward images at the fifteen roots other than root eleven, and the
inverse images at the four unmerged roots one, twelve, fourteen and fifteen. These nineteen
memberships are the explicit hypotheses of `generatedAxisGlobalTwelve_fourth_covered_of_open`;
they are not asserted here. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Fourth roots whose forward triality vector is not yet bound to the catalogue. -/
def generatedAxisGlobalTwelveFourthOpenPositive : Finset (Fin 16) :=
  {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 13, 14, 15}

/-- Unmerged Fourth roots whose inverse triality vector is not yet bound to the catalogue. -/
def generatedAxisGlobalTwelveFourthOpenNegative : Finset (Fin 16) :=
  {1, 12, 14, 15}

/-- The nineteen open Fourth vectors suffice for complete Fourth-family coverage. -/
theorem generatedAxisGlobalTwelve_fourth_covered_of_open
    (hpos : ∀ i ∈ generatedAxisGlobalTwelveFourthOpenPositive,
      sExtra (rhoLocal (generatedAxisGlobalTwelveFourthRootLocal i) generatedFourthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative)
    (hneg : ∀ i ∈ generatedAxisGlobalTwelveFourthOpenNegative,
      sExtra⁻¹ (rhoLocal (generatedAxisGlobalTwelveFourthRootLocal i) generatedFourthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative) :
    GeneratedAxisGlobalTwelveFamilyCovered 3 := by
  have hp : ∀ i : Fin 16,
      sExtra (rhoLocal (generatedAxisGlobalTwelveFourthRootLocal i) generatedFourthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
    intro i
    by_cases hi : i = 11
    · subst hi
      exact generatedAxisGlobalTwelveFourth_root11_positive
    · apply hpos i
      revert hi
      revert i
      decide
  apply generatedAxisGlobalTwelve_fourth_covered_of hp
  intro i hi
  by_cases hm : ∃ j : Fin 11, generatedAxisGlobalTwelveFourthMergedRoot j = i
  · obtain ⟨j, rfl⟩ := hm
    exact generatedAxisGlobalTwelveFourthMerged_negative_of_positive _ j (hp _)
  · apply hneg i
    revert hm hi
    revert i
    decide

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
