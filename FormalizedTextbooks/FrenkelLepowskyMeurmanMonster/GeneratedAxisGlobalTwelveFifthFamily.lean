/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveCatalogue
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalCoverageFifthActual
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalCoverageFifthPhaseReduction
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsNinthDestination
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthRoot11Orbit

/-! Binding of the actual Fifth-family transition roots to the twelve-family catalogue.

The checked fifth singular forest reduces all Fifth transitions to fourteen root words
and both triality signs; seven genuine phase merges leave twenty-one real vectors.
Five of them are bound here: roots 2, 8 and 9 are, by definition, the literal Tenth,
Root8 and Twelfth representatives; root 5 has the actual Ninth class; and the inverse
image at root 11 has the actual octad-image class. The remaining sixteen vectors are the
explicit hypotheses of `generatedAxisGlobalTwelve_fifth_covered_of`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Fifth roots whose positive triality vector is not yet bound to the catalogue. -/
def generatedAxisGlobalTwelveFifthOpenPositive : Finset (Fin 14) :=
  {0, 1, 3, 4, 6, 7, 10, 11, 12, 13}

/-- Unmerged Fifth roots whose inverse triality vector is not yet bound to the catalogue. -/
def generatedAxisGlobalTwelveFifthOpenNegative : Finset (Fin 14) :=
  {0, 1, 6, 7, 12, 13}

/-- The positive root-two transition is literally the listed Tenth representative. -/
theorem generatedAxisGlobalTwelve_fifth_root02_positive :
    sExtra (rhoLocal (generatedAxisGlobalFifthShortLocalWord 2) generatedFifthAxis) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  generatedAxisGlobalTwelve_mem_of_transport 11 1 (by
    change _ = rhoLocal 1 generatedTenthAxis
    rw [map_one, LinearEquiv.coe_one, id_eq, generatedTenthAxis_local_expression,
      generatedTenthLocal])

/-- The positive root-five transition has the actual Ninth class. -/
theorem generatedAxisGlobalTwelve_fifth_root05_positive :
    sExtra (rhoLocal (generatedAxisGlobalFifthShortLocalWord 5) generatedFifthAxis) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  generatedAxisGlobalTwelve_mem_of_class 8 generatedAxisGlobalFifthRoot05_positive_destination

/-- The positive root-eight transition is literally the listed Root8 representative. -/
theorem generatedAxisGlobalTwelve_fifth_root08_positive :
    sExtra (rhoLocal (generatedAxisGlobalFifthShortLocalWord 8) generatedFifthAxis) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  generatedAxisGlobalTwelve_mem_of_transport 9 1 (by
    change _ = rhoLocal 1 generatedFifthRootEightAxis
    rw [map_one, LinearEquiv.coe_one, id_eq, generatedFifthRootEightAxis_local_expression,
      generatedFifthRootEightLocal])

/-- The positive root-nine transition is literally the listed Twelfth representative. -/
theorem generatedAxisGlobalTwelve_fifth_root09_positive :
    sExtra (rhoLocal (generatedAxisGlobalFifthShortLocalWord 9) generatedFifthAxis) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  generatedAxisGlobalTwelve_mem_of_transport 10 1 (by
    change _ = rhoLocal 1 generatedTwelfthAxis
    rw [map_one, LinearEquiv.coe_one, id_eq, generatedTwelfthAxis_local_expression,
      generatedTwelfthLocal])

/-- The inverse root-eleven transition has the actual octad-image class. -/
theorem generatedAxisGlobalTwelve_fifth_root11_negative :
    sExtra⁻¹ (rhoLocal (generatedAxisGlobalFifthShortLocalWord 11) generatedFifthAxis) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  generatedAxisGlobalTwelve_mem_of_octad_class generatedAxisGlobalFifthRoot11_negative_destination

/-- The sixteen open Fifth vectors suffice for complete Fifth-family coverage. -/
theorem generatedAxisGlobalTwelve_fifth_covered_of
    (hpos : ∀ i ∈ generatedAxisGlobalTwelveFifthOpenPositive,
      sExtra (rhoLocal (generatedAxisGlobalFifthShortLocalWord i) generatedFifthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative)
    (hneg : ∀ i ∈ generatedAxisGlobalTwelveFifthOpenNegative,
      sExtra⁻¹ (rhoLocal (generatedAxisGlobalFifthShortLocalWord i) generatedFifthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative) :
    GeneratedAxisGlobalTwelveFamilyCovered 4 := by
  have hp : ∀ i : Fin 14,
      sExtra (rhoLocal (generatedAxisGlobalFifthShortLocalWord i) generatedFifthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
    intro i
    fin_cases i
    · exact hpos 0 (by decide)
    · exact hpos 1 (by decide)
    · exact generatedAxisGlobalTwelve_fifth_root02_positive
    · exact hpos 3 (by decide)
    · exact hpos 4 (by decide)
    · exact generatedAxisGlobalTwelve_fifth_root05_positive
    · exact hpos 6 (by decide)
    · exact hpos 7 (by decide)
    · exact generatedAxisGlobalTwelve_fifth_root08_positive
    · exact generatedAxisGlobalTwelve_fifth_root09_positive
    · exact hpos 10 (by decide)
    · exact hpos 11 (by decide)
    · exact hpos 12 (by decide)
    · exact hpos 13 (by decide)
  have hn := generatedAxisGlobalFifth_all_negative_of_phase_reduction _ hp (by
    intro i hi
    fin_cases i
    · exact hneg 0 (by decide)
    · exact hneg 1 (by decide)
    · exact absurd ⟨0, rfl⟩ hi
    · exact absurd ⟨1, rfl⟩ hi
    · exact absurd ⟨2, rfl⟩ hi
    · exact absurd ⟨3, rfl⟩ hi
    · exact hneg 6 (by decide)
    · exact hneg 7 (by decide)
    · exact absurd ⟨4, rfl⟩ hi
    · exact absurd ⟨5, rfl⟩ hi
    · exact absurd ⟨6, rfl⟩ hi
    · exact generatedAxisGlobalTwelve_fifth_root11_negative
    · exact hneg 12 (by decide)
    · exact hneg 13 (by decide))
  intro h
  exact generatedAxisGlobalFifth_triality_of_actual_destinations _ hp hn h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
