/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthFullQCentralDifference

/-! Full-Q replacement transfers attained genuine axis fixers
with the identical Conway projection. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem inclQ_projection_one (q : Q) : projH (inclQ q) = 1 := by
  change inclQ q ∈ projH.ker
  rw [← inclQ_range_eq_projH_ker]
  exact ⟨q, rfl⟩

/-- The ambiguity after genuine triality is an actual local element with trivial Conway image. -/
theorem generatedTwelfth_full_Q_triality_projection_orbit (f g : localFiberSubgroup)
    (he : spinConjugation f.val.1 = spinConjugation g.val.1) (x : GriessSpace) :
    ∃ u : H, projH u = 1 ∧ sExtra (rhoLocal (localFiberIntoH f) x) =
      rhoLocal u (sExtra (rhoLocal (localFiberIntoH g) x)) := by
  rcases generatedTwelfth_full_Q_fiber_central_difference f g he with hh | hh
  · refine ⟨1, map_one _, ?_⟩
    rw [hh, map_one]
    rfl
  · refine ⟨inclQ (qCentralInvolution * sourceOmegaQ), inclQ_projection_one _, ?_⟩
    rw [hh, map_mul, LinearEquiv.mul_apply]
    rw [← generatedTwelfth_forward_triality_central_local]
    simp only [LinearEquiv.mul_apply, LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply]

/-- Every complete candidate-axis fixer supplies an actual source-axis fixer
with the same projection. -/
theorem generatedTwelfth_full_Q_triality_fixer_transfer (f g : localFiberSubgroup)
    (he : spinConjugation f.val.1 = spinConjugation g.val.1) (x : GriessSpace) (h : H)
    (hfix : rhoLocal h (sExtra (rhoLocal (localFiberIntoH g) x)) =
      sExtra (rhoLocal (localFiberIntoH g) x)) :
    ∃ k : H, projH k = projH h ∧
      rhoLocal k (sExtra (rhoLocal (localFiberIntoH f) x)) =
        sExtra (rhoLocal (localFiberIntoH f) x) := by
  obtain ⟨u, hu, hx⟩ := generatedTwelfth_full_Q_triality_projection_orbit f g he x
  refine ⟨u * h * u⁻¹, ?_, ?_⟩
  · simp only [map_mul, map_inv, hu, one_mul, inv_one, mul_one]
  · rw [hx, map_mul, map_mul, map_inv]
    simp only [LinearEquiv.mul_apply, LinearEquiv.coe_inv,
      LinearEquiv.symm_apply_apply, hfix]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
