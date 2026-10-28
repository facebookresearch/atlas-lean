/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddOmega
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFamilyOrbits
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisPairLocal

/-! Both frame-root outputs have genuine full local destinations in the original axis model. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The positive frame-root output has the actual odd-axis local class. -/
theorem generatedAxisGlobalOddOmega_positive_destination :
    Quotient.mk (MulAction.orbitRel H GriessSpace)
      (sExtra (rhoLocal (generatedAxisGlobalOddSourceRootLocalWord 5) generatedOddAxis)) =
      Quotient.mk (MulAction.orbitRel H GriessSpace) generatedOddAxis := by
  apply (generatedAxis_local_class_eq_iff _ _).mpr
  obtain ⟨h, hh⟩ := generatedAxisGlobalOddOmega_positive_orbit
  refine ⟨h⁻¹, ?_⟩
  rw [hh, map_inv, LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply]

/-- The inverse frame-root output has the actual original coordinate-pair axis local class. -/
theorem generatedAxisGlobalOddOmega_negative_destination :
    Quotient.mk (MulAction.orbitRel H GriessSpace)
      (sExtra⁻¹ (rhoLocal (generatedAxisGlobalOddSourceRootLocalWord 5) generatedOddAxis)) =
      Quotient.mk (MulAction.orbitRel H GriessSpace) (conwayAxis 0) := by
  apply (generatedAxis_local_class_eq_iff _ _).mpr
  obtain ⟨h, hh⟩ := generatedAxis_local_signed_transitive
    (Sum.inr (Sum.inr (0, 0))) (Sum.inl (0, 0)) 0 0
  refine ⟨h, ?_⟩
  rw [generatedAxisGlobalOddOmega_negative]
  simpa only [conwayShortAxis_pair_zero] using hh

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
