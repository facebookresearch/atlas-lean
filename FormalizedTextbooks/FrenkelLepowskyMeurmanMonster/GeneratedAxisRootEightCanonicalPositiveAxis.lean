/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightCanonicalPositiveFiber
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightIncomingSpatialAction

/-! The explicitly positive canonical axis belongs to the entire original root-eight local orbit. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The entire genuine positive canonical image of the full positive incoming triality axis. -/
def generatedRootEightCanonicalPositiveAxis : GriessSpace :=
  rhoLocal generatedRootEightCanonicalPositiveLocal
    generatedRootEightIncomingPositiveTrialityDestination

/-- A genuine local transporter connects the positive canonical axis and the original root-eight axis. -/
theorem generatedRootEight_canonical_positive_axis_orbit :
    ∃ h : H, generatedFifthRootEightAxis =
      rhoLocal h generatedRootEightCanonicalPositiveAxis := by
  obtain ⟨u, _, hu⟩ := generatedRootEight_incoming_positive_projection_orbit
  refine ⟨u * generatedRootEightCanonicalPositiveLocal⁻¹, ?_⟩
  rw [generatedRootEightCanonicalPositiveAxis, map_mul, map_inv]
  simp only [LinearEquiv.mul_apply, LinearEquiv.coe_inv,
    LinearEquiv.symm_apply_apply]
  exact hu

/-- An actual whole canonical-axis fixer supplies a whole original-axis fixer with the transported image. -/
theorem generatedRootEight_canonical_positive_fixer_transfer (h : H)
    (hfix : rhoLocal h generatedRootEightCanonicalPositiveAxis =
      generatedRootEightCanonicalPositiveAxis) :
    ∃ k : H,
      projH k = (projH generatedRootEightCanonicalPositiveLocal)⁻¹ * projH h *
        projH generatedRootEightCanonicalPositiveLocal ∧
      rhoLocal k generatedFifthRootEightAxis = generatedFifthRootEightAxis := by
  obtain ⟨u, hu, hx⟩ := generatedRootEight_incoming_positive_projection_orbit
  let v := u * generatedRootEightCanonicalPositiveLocal⁻¹
  have hv : generatedFifthRootEightAxis = rhoLocal v generatedRootEightCanonicalPositiveAxis := by
    rw [generatedRootEightCanonicalPositiveAxis, map_mul, map_inv]
    simp only [LinearEquiv.mul_apply, LinearEquiv.coe_inv,
      LinearEquiv.symm_apply_apply]
    exact hx
  refine ⟨v * h * v⁻¹, ?_, ?_⟩
  · simp only [v, map_mul, map_inv, hu, one_mul]
    group
  · rw [hv, map_mul, map_mul, map_inv]
    simp only [LinearEquiv.mul_apply, LinearEquiv.coe_inv,
      LinearEquiv.symm_apply_apply, hfix]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
