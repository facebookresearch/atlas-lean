/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsNinthRoot05Orbit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFamilyOrbits

/-! Both actual fifth root-five transitions have the genuine local class
of the literal ninth prototype, with every source constituent retained. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The local orbit class of the literal ninth actual generated axis. -/
def generatedAxisGlobalNinthDestination : generatedAxisLocalOrbitSpace :=
  Quotient.mk (MulAction.orbitRel H GriessSpace) generatedNinthAxis

/-- The complete positive root-five output has the actual ninth local destination. -/
theorem generatedAxisGlobalFifthRoot05_positive_destination :
    Quotient.mk (MulAction.orbitRel H GriessSpace)
      (sExtra (rhoLocal (generatedAxisGlobalFifthShortLocalWord 5) generatedFifthAxis)) =
        generatedAxisGlobalNinthDestination := by
  apply (generatedAxis_local_class_eq_iff _ _).mpr
  obtain ⟨k, hk⟩ := generatedAxisGlobalNinthRoot05_positive_orbit
  refine ⟨k⁻¹, ?_⟩
  rw [hk, map_inv, LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply]

/-- The complete inverse root-five output has the same actual ninth local destination. -/
theorem generatedAxisGlobalFifthRoot05_negative_destination :
    Quotient.mk (MulAction.orbitRel H GriessSpace)
      (sExtra⁻¹ (rhoLocal (generatedAxisGlobalFifthShortLocalWord 5) generatedFifthAxis)) =
        generatedAxisGlobalNinthDestination := by
  apply (generatedAxis_local_class_eq_iff _ _).mpr
  obtain ⟨k, hk⟩ := generatedAxisGlobalNinthRoot05_negative_orbit
  refine ⟨k⁻¹, ?_⟩
  rw [hk, map_inv, LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
