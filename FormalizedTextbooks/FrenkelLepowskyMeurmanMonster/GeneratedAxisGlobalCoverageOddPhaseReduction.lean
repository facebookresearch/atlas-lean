/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddPhaseRoots

/-! Genuine phase-merged roots reduce the real destination obligations from
eighteen to eleven, without assuming any global axis classification. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- A positive local class binding at a phase-merged root also binds its inverse image. -/
theorem generatedAxisGlobalOddPhaseRootIndex_negative_of_positive {ι : Type*}
    (v : ι → GriessSpace) (j : Fin 7)
    (hpositive : sExtra (rhoLocal (generatedAxisGlobalOddSourceRootLocalWord
      (generatedAxisGlobalOddPhaseRootIndex j)) generatedOddAxis) ∈ generatedLocalOrbitUnion v) :
    sExtra⁻¹ (rhoLocal (generatedAxisGlobalOddSourceRootLocalWord
      (generatedAxisGlobalOddPhaseRootIndex j)) generatedOddAxis) ∈ generatedLocalOrbitUnion v := by
  obtain ⟨k, hk⟩ := generatedAxisGlobalOdd_phase_merge j
  have he : sExtra⁻¹ (rhoLocal (generatedAxisGlobalOddSourceRootLocalWord
      (generatedAxisGlobalOddPhaseRootIndex j)) generatedOddAxis) =
      rhoLocal k⁻¹ (sExtra (rhoLocal (generatedAxisGlobalOddSourceRootLocalWord
        (generatedAxisGlobalOddPhaseRootIndex j)) generatedOddAxis)) := by
    rw [hk, map_inv]
    simp only [LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply]
  rw [he]
  exact generatedLocalOrbitUnion_local v k⁻¹ hpositive

/-- Nine positive and only the two remaining inverse destination bindings give all signs. -/
theorem generatedAxisGlobalOdd_all_negative_of_phase_reduction {ι : Type*}
    (v : ι → GriessSpace)
    (hpositive : ∀ i : Fin 9,
      sExtra (rhoLocal (generatedAxisGlobalOddSourceRootLocalWord i) generatedOddAxis) ∈
        generatedLocalOrbitUnion v)
    (hnegative : ∀ i : Fin 9, (¬∃ j : Fin 7, generatedAxisGlobalOddPhaseRootIndex j = i) →
      sExtra⁻¹ (rhoLocal (generatedAxisGlobalOddSourceRootLocalWord i) generatedOddAxis) ∈
        generatedLocalOrbitUnion v) :
    ∀ i : Fin 9,
      sExtra⁻¹ (rhoLocal (generatedAxisGlobalOddSourceRootLocalWord i) generatedOddAxis) ∈
        generatedLocalOrbitUnion v := by
  intro i
  by_cases hi : ∃ j : Fin 7, generatedAxisGlobalOddPhaseRootIndex j = i
  · obtain ⟨j, rfl⟩ := hi
    exact generatedAxisGlobalOddPhaseRootIndex_negative_of_positive v j (hpositive _)
  · exact hnegative i hi

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
