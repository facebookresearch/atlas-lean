/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveCatalogue
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalCoverageFirstLayer

/-! Complete triality coverage of the actual First family by the twelve-family catalogue.
The proved first transition layer has the three local destinations First, Octad and Odd;
each is bound to its listed representative by an explicit local transport. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The listed First representative is the original coordinate-pair axis. -/
theorem generatedAxisGlobalTwelveRepresentative_first :
    generatedAxisGlobalTwelveRepresentative 0 = conwayAxis 0 :=
  conwayShortAxis_pair_zero 0

/-- Each of the three first-layer representatives lies in the twelve-family union. -/
theorem generatedAxisGlobalTwelve_firstLayer_mem (i : Fin 3) :
    generatedAxisGlobalFirstLayer i ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  fin_cases i
  · exact generatedAxisGlobalTwelve_mem_of_transport 0 1 (by
      rw [map_one, generatedAxisGlobalTwelveRepresentative_first]
      rfl)
  · exact generatedAxisGlobalTwelve_mem_of_octad_class rfl
  · exact generatedAxisGlobalTwelve_mem_of_transport 2 1 (by
      rw [map_one]
      rfl)

/-- Every actual triality transition of the First family lies in the catalogue union. -/
theorem generatedAxisGlobalTwelve_first_covered : GeneratedAxisGlobalTwelveFamilyCovered 0 := by
  intro h
  rw [generatedAxisGlobalTwelveRepresentative_first]
  obtain ⟨i, k, hk⟩ := generatedAxisGlobalFirstLayer_covers_first_step h
  rw [← hk]
  exact generatedLocalOrbitUnion_local _ k (generatedAxisGlobalTwelve_firstLayer_mem i)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
