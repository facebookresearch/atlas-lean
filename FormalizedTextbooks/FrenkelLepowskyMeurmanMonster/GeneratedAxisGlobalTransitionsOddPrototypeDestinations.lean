/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddPrototypeOrbits
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFamilyOrbits

/-! Six complete real odd-family root outputs have genuine frozen prototype destination classes. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Actual local classes of the frozen sixth, seventh and eighth prototypes. -/
def generatedAxisGlobalOddPrototypeDestination (j : Fin 3) : generatedAxisLocalOrbitSpace :=
  Quotient.mk (MulAction.orbitRel H GriessSpace) (generatedAxisGlobalOddPrototypeAxis j)

/-- Each positive root output has the corresponding actual full prototype local destination. -/
theorem generatedAxisGlobalOddPrototype_positive_destination (j : Fin 3) :
    Quotient.mk (MulAction.orbitRel H GriessSpace)
      (sExtra (rhoLocal (generatedAxisGlobalOddSourceRootLocalWord
        (generatedAxisGlobalOddPrototypeRootIndex j)) generatedOddAxis)) =
      generatedAxisGlobalOddPrototypeDestination j := by
  apply (generatedAxis_local_class_eq_iff _ _).mpr
  obtain ⟨k, hk⟩ := generatedAxisGlobalOddPrototype_positive_orbit j
  refine ⟨k⁻¹, ?_⟩
  rw [hk, map_inv, LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply]

/-- Each inverse root output has the same corresponding actual full prototype destination. -/
theorem generatedAxisGlobalOddPrototype_negative_destination (j : Fin 3) :
    Quotient.mk (MulAction.orbitRel H GriessSpace)
      (sExtra⁻¹ (rhoLocal (generatedAxisGlobalOddSourceRootLocalWord
        (generatedAxisGlobalOddPrototypeRootIndex j)) generatedOddAxis)) =
      generatedAxisGlobalOddPrototypeDestination j := by
  apply (generatedAxis_local_class_eq_iff _ _).mpr
  obtain ⟨k, hk⟩ := generatedAxisGlobalOddPrototype_negative_orbit j
  refine ⟨k⁻¹, ?_⟩
  rw [hk, map_inv, LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
