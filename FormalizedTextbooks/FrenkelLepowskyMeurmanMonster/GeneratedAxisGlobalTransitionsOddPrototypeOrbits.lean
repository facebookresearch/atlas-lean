/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddPrototypeRoots
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddPhaseRoots
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthRootClassRelation

/-! Six genuine full-vector destinations of odd-family triality root transitions. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The frozen actual sixth, seventh and eighth axes, with their complete original source words. -/
def generatedAxisGlobalOddPrototypeAxis : Fin 3 → GriessSpace :=
  ![generatedSixthAxis, generatedSeventhAxis, generatedEighthAxis]

/-- Their full actual odd-axis source expressions. -/
theorem generatedAxisGlobalOddPrototypeAxis_local (k : Fin 3) :
    generatedAxisGlobalOddPrototypeAxis k =
      sExtra (rhoLocal (generatedAxisGlobalOddPrototypeLocal k) generatedOddAxis) := by
  fin_cases k <;> rfl

/-- Indices of the actual full-axis Q fixers for these three prototype roots. -/
def generatedAxisGlobalOddPrototypePhaseIndex : Fin 3 → Fin 7 := ![6, 5, 1]

/-- Each genuine phase fixer is attached to precisely the corresponding actual binary root. -/
theorem generatedAxisGlobalOddPrototypePhaseIndex_actual : ∀ k : Fin 3,
    generatedAxisGlobalOddPhaseRootIndex (generatedAxisGlobalOddPrototypePhaseIndex k) =
      generatedAxisGlobalOddPrototypeRootIndex k := by
  decide +kernel

private theorem prototypeRoot_phase (k : Fin 3) :
    ∃ h : H,
      sExtra (rhoLocal (generatedAxisGlobalOddSourceRootLocalWord
        (generatedAxisGlobalOddPrototypeRootIndex k)) generatedOddAxis) =
      rhoLocal h (sExtra⁻¹ (rhoLocal (generatedAxisGlobalOddSourceRootLocalWord
        (generatedAxisGlobalOddPrototypeRootIndex k)) generatedOddAxis)) := by
  simpa only [generatedAxisGlobalOddPrototypePhaseIndex_actual k] using
    generatedAxisGlobalOdd_phase_merge (generatedAxisGlobalOddPrototypePhaseIndex k)

/-- The three positive root transitions are full actual local images of the frozen prototypes. -/
theorem generatedAxisGlobalOddPrototype_positive_orbit (j : Fin 3) :
    ∃ h : H,
      sExtra (rhoLocal (generatedAxisGlobalOddSourceRootLocalWord
        (generatedAxisGlobalOddPrototypeRootIndex j)) generatedOddAxis) =
      rhoLocal h (generatedAxisGlobalOddPrototypeAxis j) := by
  have hfix : rhoLocal (generatedAxisGlobalOddPrototypeTransport j).val generatedOddAxis =
      generatedOddAxis := (generatedAxisGlobalOddPrototypeTransport j).property
  have hrel := generatedAxisGlobal_triality_root_relation generatedOddAxis
    (generatedAxisGlobalOddPrototypeLocal j)
    (generatedAxisGlobalOddSourceRootLocalWord (generatedAxisGlobalOddPrototypeRootIndex j))
    (generatedAxisGlobalOddPrototypeTransport j).val hfix
    (generatedAxisGlobalOddPrototypeTransport_actual j)
  rw [← generatedAxisGlobalOddPrototypeAxis_local] at hrel
  rcases hrel with ⟨k, hk⟩ | ⟨k, hk⟩
  · refine ⟨k⁻¹, ?_⟩
    rw [hk, map_inv, LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply]
  · obtain ⟨m, hm⟩ := prototypeRoot_phase j
    refine ⟨m * k⁻¹, ?_⟩
    rw [hk, map_mul, LinearEquiv.mul_apply, map_inv]
    simp only [LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply]
    exact hm

/-- All three inverse root transitions lie in the same genuine full prototype local classes. -/
theorem generatedAxisGlobalOddPrototype_negative_orbit (j : Fin 3) :
    ∃ h : H,
      sExtra⁻¹ (rhoLocal (generatedAxisGlobalOddSourceRootLocalWord
        (generatedAxisGlobalOddPrototypeRootIndex j)) generatedOddAxis) =
      rhoLocal h (generatedAxisGlobalOddPrototypeAxis j) := by
  obtain ⟨k, hk⟩ := generatedAxisGlobalOddPrototype_positive_orbit j
  obtain ⟨m, hm⟩ := prototypeRoot_phase j
  refine ⟨m⁻¹ * k, ?_⟩
  rw [map_mul, LinearEquiv.mul_apply, ← hk, hm, map_inv]
  simp only [LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
