/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFifthFamily
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFifthBindRoot11
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFifthBindRoot13

/-! Fifth-family coverage reduced to thirteen open transition vectors.

Of the sixteen open Fifth vectors of `generatedAxisGlobalTwelve_fifth_covered_of`, three are
bound here: the positive root-eleven vector (Fifth class, by the octad-side phase merge) and
both root-thirteen vectors (Odd and Fifth classes, by reversing the Odd root-three transports).
The remaining thirteen vectors are explicit hypotheses; this is not a coverage proof. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Fifth roots whose positive triality vector is still unbound. -/
def generatedAxisGlobalTwelveFifthBindOpenPositive : Finset (Fin 14) :=
  {0, 1, 3, 4, 6, 7, 10, 12}

/-- Unmerged Fifth roots whose inverse triality vector is still unbound. -/
def generatedAxisGlobalTwelveFifthBindOpenNegative : Finset (Fin 14) :=
  {0, 1, 6, 7, 12}

/-- The thirteen remaining Fifth vectors suffice for complete Fifth-family coverage. -/
theorem generatedAxisGlobalTwelveFifthBind_covered_of
    (hpos : ∀ i ∈ generatedAxisGlobalTwelveFifthBindOpenPositive,
      sExtra (rhoLocal (generatedAxisGlobalFifthShortLocalWord i) generatedFifthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative)
    (hneg : ∀ i ∈ generatedAxisGlobalTwelveFifthBindOpenNegative,
      sExtra⁻¹ (rhoLocal (generatedAxisGlobalFifthShortLocalWord i) generatedFifthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative) :
    GeneratedAxisGlobalTwelveFamilyCovered 4 := by
  apply generatedAxisGlobalTwelve_fifth_covered_of
  · intro i hi
    fin_cases i <;> simp [generatedAxisGlobalTwelveFifthOpenPositive] at hi
    · exact hpos 0 (by decide)
    · exact hpos 1 (by decide)
    · exact hpos 3 (by decide)
    · exact hpos 4 (by decide)
    · exact hpos 6 (by decide)
    · exact hpos 7 (by decide)
    · exact hpos 10 (by decide)
    · exact generatedAxisGlobalTwelveFifthBind_root11_positive
    · exact hpos 12 (by decide)
    · exact generatedAxisGlobalTwelveFifthBind_root13.1
  · intro i hi
    fin_cases i <;> simp [generatedAxisGlobalTwelveFifthOpenNegative] at hi
    · exact hneg 0 (by decide)
    · exact hneg 1 (by decide)
    · exact hneg 6 (by decide)
    · exact hneg 7 (by decide)
    · exact hneg 12 (by decide)
    · exact generatedAxisGlobalTwelveFifthBind_root13.2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
