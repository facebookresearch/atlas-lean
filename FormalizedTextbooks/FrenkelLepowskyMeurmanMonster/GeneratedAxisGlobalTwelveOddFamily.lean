/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveCatalogue
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalCoverageOddActual
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalCoverageOddPhaseReduction
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddComparisonEqualities
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthDestinationEqualities
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFifthDestinationEqualities
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddPrototypeDestinations
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddOmegaDestinations
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot06OctadDestination

/-! Complete triality coverage of the actual Odd family by the twelve-family catalogue.

The checked odd singular forest reduces every Odd transition to nine root words and
both triality signs; seven genuine phase merges leave nine positive and two inverse
real vectors. Each of the eleven is bound to a listed representative: roots 0, 5 and
the inverse at root 6 to Odd, root 1 to Eighth, roots 2 and 4 to Fourth, root 3 to Fifth,
root 6 to Octad, root 7 to Seventh, root 8 to Sixth, and the inverse at root 5 to First. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The positive root-8 transition binds to the listed Sixth representative. -/
theorem generatedAxisGlobalTwelve_odd_root08_positive :
    sExtra (rhoLocal (generatedAxisGlobalOddSourceRootLocalWord 8) generatedOddAxis) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  obtain ⟨k, hk⟩ := generatedAxisGlobalOddPrototype_positive_orbit 0
  simp only [generatedAxisGlobalOddPrototypeRootIndex, generatedAxisGlobalOddPrototypeAxis,
    Matrix.cons_val] at hk
  rw [hk]
  refine generatedLocalOrbitUnion_local _ k ⟨5, 1, ?_⟩
  simp only [generatedAxisGlobalTwelveRepresentative, Matrix.cons_val, map_one,
    LinearEquiv.coe_one, id_eq]

/-- The positive root-7 transition binds to the listed Seventh representative. -/
theorem generatedAxisGlobalTwelve_odd_root07_positive :
    sExtra (rhoLocal (generatedAxisGlobalOddSourceRootLocalWord 7) generatedOddAxis) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  obtain ⟨k, hk⟩ := generatedAxisGlobalOddPrototype_positive_orbit 1
  simp only [generatedAxisGlobalOddPrototypeRootIndex, generatedAxisGlobalOddPrototypeAxis,
    Matrix.cons_val] at hk
  rw [hk]
  refine generatedLocalOrbitUnion_local _ k ⟨6, 1, ?_⟩
  simp only [generatedAxisGlobalTwelveRepresentative, Matrix.cons_val, map_one,
    LinearEquiv.coe_one, id_eq]

/-- The positive root-1 transition binds to the listed Eighth representative. -/
theorem generatedAxisGlobalTwelve_odd_root01_positive :
    sExtra (rhoLocal (generatedAxisGlobalOddSourceRootLocalWord 1) generatedOddAxis) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  obtain ⟨k, hk⟩ := generatedAxisGlobalOddPrototype_positive_orbit 2
  simp only [generatedAxisGlobalOddPrototypeRootIndex, generatedAxisGlobalOddPrototypeAxis,
    Matrix.cons_val] at hk
  rw [hk]
  refine generatedLocalOrbitUnion_local _ k ⟨7, 1, ?_⟩
  simp only [generatedAxisGlobalTwelveRepresentative, Matrix.cons_val, map_one,
    LinearEquiv.coe_one, id_eq]

/-- Every positive Odd root transition lies in the twelve-family union. -/
theorem generatedAxisGlobalTwelve_odd_positive (i : Fin 9) :
    sExtra (rhoLocal (generatedAxisGlobalOddSourceRootLocalWord i) generatedOddAxis) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  fin_cases i
  · exact generatedAxisGlobalTwelve_mem_of_transport 2 _
      generatedAxisGlobalOddRoot00_positive_comparison
  · exact generatedAxisGlobalTwelve_odd_root01_positive
  · obtain ⟨k, hk⟩ := generatedAxisGlobalOddRoot02_positive_fourth_destination
    exact generatedAxisGlobalTwelve_mem_of_transport 3 k hk
  · obtain ⟨k, hk⟩ := generatedAxisGlobalOddRoot03_positive_fifth_destination
    exact generatedAxisGlobalTwelve_mem_of_transport 4 k hk
  · obtain ⟨k, hk⟩ := generatedAxisGlobalOddRoot04_positive_fourth_destination
    exact generatedAxisGlobalTwelve_mem_of_transport 3 k hk
  · exact generatedAxisGlobalTwelve_mem_of_class 2 generatedAxisGlobalOddOmega_positive_destination
  · exact generatedAxisGlobalTwelve_mem_of_octad_class
      generatedAxisGlobalOddRoot06_positive_destination
  · exact generatedAxisGlobalTwelve_odd_root07_positive
  · exact generatedAxisGlobalTwelve_odd_root08_positive

/-- The inverse root-five transition has the class of the listed First representative. -/
theorem generatedAxisGlobalTwelve_odd_root05_negative :
    sExtra⁻¹ (rhoLocal (generatedAxisGlobalOddSourceRootLocalWord 5) generatedOddAxis) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  apply generatedAxisGlobalTwelve_mem_of_class 0
  rw [generatedAxisGlobalOddOmega_negative_destination, ← conwayShortAxis_pair_zero]
  rfl

/-- The inverse root-six transition is an explicit local image of the Odd representative. -/
theorem generatedAxisGlobalTwelve_odd_root06_negative :
    sExtra⁻¹ (rhoLocal (generatedAxisGlobalOddSourceRootLocalWord 6) generatedOddAxis) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  generatedAxisGlobalTwelve_mem_of_transport 2 _ generatedAxisGlobalOddRoot06_negative_comparison

/-- Every actual triality transition of the Odd family lies in the catalogue union. -/
theorem generatedAxisGlobalTwelve_odd_covered : GeneratedAxisGlobalTwelveFamilyCovered 2 := by
  have hn := generatedAxisGlobalOdd_all_negative_of_phase_reduction _
    generatedAxisGlobalTwelve_odd_positive (by
      intro i hi
      fin_cases i
      · exact absurd ⟨0, rfl⟩ hi
      · exact absurd ⟨1, rfl⟩ hi
      · exact absurd ⟨2, rfl⟩ hi
      · exact absurd ⟨3, rfl⟩ hi
      · exact absurd ⟨4, rfl⟩ hi
      · exact generatedAxisGlobalTwelve_odd_root05_negative
      · exact generatedAxisGlobalTwelve_odd_root06_negative
      · exact absurd ⟨5, rfl⟩ hi
      · exact absurd ⟨6, rfl⟩ hi)
  intro h
  exact generatedAxisGlobalOdd_triality_of_actual_destinations _
    generatedAxisGlobalTwelve_odd_positive hn h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
