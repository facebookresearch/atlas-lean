/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsNinthBinaryRoot
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthRootClassRelation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthRoot05Phase

/-! Actual full-vector identification of both root-five triality destinations
with the literal ninth prototype. The extraspecial sign is explicitly resolved. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The genuine ninth axis and positive root-five transition have the same full local orbit. -/
theorem generatedAxisGlobalNinthRoot05_positive_orbit :
    ∃ k : H, sExtra (rhoLocal (generatedAxisGlobalFifthShortLocalWord 5) generatedFifthAxis) =
      rhoLocal k generatedNinthAxis := by
  have hfix : rhoLocal generatedAxisGlobalNinthRootTransport.val generatedFifthAxis =
      generatedFifthAxis := generatedAxisGlobalNinthRootTransport.property
  have hrel := generatedAxisGlobal_triality_root_relation generatedFifthAxis
    (localFiberIntoH generatedNinthLocalFiber) (generatedAxisGlobalFifthShortLocalWord 5)
    generatedAxisGlobalNinthRootTransport.val hfix generatedAxisGlobalNinthRootTransport_actual
  rw [← generatedNinthAxis_local_expression] at hrel
  rcases hrel with ⟨k, hk⟩ | ⟨k, hk⟩
  · refine ⟨k⁻¹, ?_⟩
    rw [hk, map_inv, LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply]
  · obtain ⟨m, hm⟩ := generatedAxisGlobalFifthRoot05_phase_merge
    refine ⟨m * k⁻¹, ?_⟩
    rw [hk, map_mul, LinearEquiv.mul_apply, map_inv]
    simp only [LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply]
    exact hm

/-- The inverse root-five transition also has the same genuine full-vector ninth local orbit. -/
theorem generatedAxisGlobalNinthRoot05_negative_orbit :
    ∃ k : H, sExtra⁻¹
      (rhoLocal (generatedAxisGlobalFifthShortLocalWord 5) generatedFifthAxis) =
        rhoLocal k generatedNinthAxis := by
  obtain ⟨k, hk⟩ := generatedAxisGlobalNinthRoot05_positive_orbit
  obtain ⟨m, hm⟩ := generatedAxisGlobalFifthRoot05_phase_merge
  refine ⟨m⁻¹ * k, ?_⟩
  rw [map_mul, LinearEquiv.mul_apply, ← hk, hm, map_inv]
  simp only [LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
