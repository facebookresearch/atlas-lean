/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8FrameSystemsOrbitAction
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthSectionRootAction

/-! Every parent-tree letter is an original isometry in the full selected-section group. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- All eighteen original signs, selected permutations and Xi preserve the selected section. -/
theorem generatedAxisE8FrameSystemOrbitGenerator_mem (g : Fin 18) :
    generatedFifthSectionGenerator g ∈ generatedAxisE8FrameSystemSectionGroup := by
  rw [generatedAxisE8SectionStabilizer_mem]
  by_cases h : g.val < 12
  · simp only [generatedFifthSectionGenerator, h, ↓reduceDIte]
    exact generatedAxisE8_preserving_image _ _ (generatedAxisE8_sign_preserves _ _)
  · by_cases h' : g.val < 17
    · simp only [generatedFifthSectionGenerator, h, h', ↓reduceDIte]
      rw [generatedAxisE8_permutation_image,
        (generatedFifthSelectedOctadSubgroup_mem _).mp
          (generatedFifthSelectedOctad_generator_mem _)]
    · have hg : g = 17 := Fin.ext (by omega)
      subst g
      change generatedAxisE8ImageSection co1XiIsometry
        (golayOctadWord generatedFifthFlagOctad) = _
      exact ((generatedAxisE8FrameSystemStabilizer_mem _ _ _).mp
        generatedFifthFrameSystem_xi_mem).1

/-- Each finite parent-tree letter as an element of the full actual section group. -/
def generatedAxisE8FrameSystemOrbitLetter (g : Fin 18) :
    generatedAxisE8FrameSystemSectionGroup :=
  ⟨generatedFifthSectionGenerator g, generatedAxisE8FrameSystemOrbitGenerator_mem g⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
