/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedNormalTrialityOmega

/-! Genuine local-Q transport of an unresolved incoming tensor sign through triality.
These symbolic proofs are uncompiled drafts; no source spin orientation is selected. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The first triality conjugate of the local central involution is the genuine local
extraspecial element obtained by multiplying that involution by the original source Omega. -/
theorem generatedTenth_source_central_triality_conjugate :
    sExtra * localCentralGriess * sExtra⁻¹ =
      rhoLocal (inclQ (qCentralInvolution * sourceOmegaQ)) := by
  have hsign : trialityCentralSign 0 * trialityCentralSign 2 =
      trialityCentralSign 1 := by
    rw [← trialityCentralSign_zero_mul_one, ← mul_assoc,
      trialityCentralSign_square, one_mul]
  calc
    _ = trialityCentralSign 1 := localCentralGriess_conjugate
    _ = trialityCentralSign 0 * trialityCentralSign 2 := hsign.symm
    _ = rhoLocal (inclQ qCentralInvolution) * rhoLocal (inclQ sourceOmegaQ) := by
      rw [← localCentralGriess_eq_trialityCentralSign,
        ← sourceOmegaQ_eq_trialityCentralSign]
      rfl
    _ = rhoLocal (inclQ (qCentralInvolution * sourceOmegaQ)) := by
      rw [map_mul, map_mul]

/-- An incoming axis differing only by the genuine central tensor sign has a post-triality
image in the same actual local-H orbit. The complete Griess vectors are retained. -/
theorem generatedTenth_source_central_triality_vector_transport
    (a b : GriessSpace) (hab : a = b ∨ a = localCentralGriess b) :
    ∃ h : H, sExtra a = rhoLocal h (sExtra b) := by
  rcases hab with hab | hab
  · refine ⟨1, ?_⟩
    rw [hab, map_one]
    rfl
  · refine ⟨inclQ (qCentralInvolution * sourceOmegaQ), ?_⟩
    rw [hab]
    have h := LinearEquiv.congr_fun generatedTenth_source_central_triality_conjugate
      (sExtra b)
    simpa only [LinearEquiv.mul_apply, LinearEquiv.coe_inv,
      LinearEquiv.symm_apply_apply] using h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
