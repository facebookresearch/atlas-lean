/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthPhaseRoots

/-! Genuine phase-merged roots reduce the real destination obligations from
twenty-eight to twenty-one, without assuming any global axis classification. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- A positive local class binding at a phase-merged root also binds its inverse image. -/
theorem generatedAxisGlobalFifthMergedRoot_negative_of_positive {ι : Type*}
    (v : ι → GriessSpace) (j : Fin 7)
    (hpositive : sExtra (rhoLocal (generatedAxisGlobalFifthShortLocalWord
      (generatedAxisGlobalFifthMergedRoot j)) generatedFifthAxis) ∈ generatedLocalOrbitUnion v) :
    sExtra⁻¹ (rhoLocal (generatedAxisGlobalFifthShortLocalWord
      (generatedAxisGlobalFifthMergedRoot j)) generatedFifthAxis) ∈ generatedLocalOrbitUnion v := by
  obtain ⟨k, hk⟩ := generatedAxisGlobalFifthMergedRoot_orbit j
  have he : sExtra⁻¹ (rhoLocal (generatedAxisGlobalFifthShortLocalWord
      (generatedAxisGlobalFifthMergedRoot j)) generatedFifthAxis) =
      rhoLocal k⁻¹ (sExtra (rhoLocal (generatedAxisGlobalFifthShortLocalWord
        (generatedAxisGlobalFifthMergedRoot j)) generatedFifthAxis)) := by
    rw [hk, map_inv]
    simp only [LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply]
  rw [he]
  exact generatedLocalOrbitUnion_local v k⁻¹ hpositive

/-- Fourteen positive and only the seven remaining inverse destination bindings give all signs. -/
theorem generatedAxisGlobalFifth_all_negative_of_phase_reduction {ι : Type*}
    (v : ι → GriessSpace)
    (hpositive : ∀ i : Fin 14,
      sExtra (rhoLocal (generatedAxisGlobalFifthShortLocalWord i) generatedFifthAxis) ∈
        generatedLocalOrbitUnion v)
    (hnegative : ∀ i : Fin 14, (¬∃ j : Fin 7, generatedAxisGlobalFifthMergedRoot j = i) →
      sExtra⁻¹ (rhoLocal (generatedAxisGlobalFifthShortLocalWord i) generatedFifthAxis) ∈
        generatedLocalOrbitUnion v) :
    ∀ i : Fin 14,
      sExtra⁻¹ (rhoLocal (generatedAxisGlobalFifthShortLocalWord i) generatedFifthAxis) ∈
        generatedLocalOrbitUnion v := by
  intro i
  by_cases hi : ∃ j : Fin 7, generatedAxisGlobalFifthMergedRoot j = i
  · obtain ⟨j, rfl⟩ := hi
    exact generatedAxisGlobalFifthMergedRoot_negative_of_positive v j (hpositive _)
  · exact hnegative i hi

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
