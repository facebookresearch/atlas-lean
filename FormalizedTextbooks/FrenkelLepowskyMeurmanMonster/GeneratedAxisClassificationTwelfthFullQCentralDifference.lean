/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedNormalOrbit

/-! Full extraspecial conjugation fixes a local lift up to the central sign.
Triality sends that ambiguity into actual H, so the final axes have identical local orbits. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Genuine local fibers with identical full-Q conjugation differ only by actual central Q. -/
theorem generatedTwelfth_full_Q_fiber_central_difference (f g : localFiberSubgroup)
    (he : spinConjugation f.val.1 = spinConjugation g.val.1) :
    localFiberIntoH f = localFiberIntoH g ∨
      localFiberIntoH f = inclQ qCentralInvolution * localFiberIntoH g := by
  let d : localFiberSubgroup := f * g⁻¹
  have hs : spinConjugation d.val.1 = 1 := by
    change spinConjugation (f.val.1 * g.val.1⁻¹) = 1
    rw [map_mul, map_inv, he, mul_inv_cancel]
  have hc : localFiberIntoH d ∈ Subgroup.centralizer (inclQ.range : Set H) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro a ⟨q, rfl⟩
    have h := inclQ_spinConjugation d q
    rw [hs, MulAut.one_apply] at h
    calc
      inclQ q * localFiberIntoH d =
          (localFiberIntoH d * inclQ q * (localFiberIntoH d)⁻¹) *
            localFiberIntoH d := by rw [← h]
      _ = localFiberIntoH d * inclQ q := by group
  obtain ⟨q, hq⟩ := local_centralizer_q_le_q hc
  have hqc : q ∈ centerQ := by
    change q ∈ Subgroup.center Q
    rw [Subgroup.mem_center_iff]
    intro a
    apply inclQ_injective
    rw [map_mul, map_mul]
    have h := Subgroup.mem_centralizer_iff.mp hc (inclQ a) ⟨a, rfl⟩
    rw [← hq] at h
    exact h
  have hh := congrArg (fun h : H => h * localFiberIntoH g) hq
  change inclQ q * localFiberIntoH g = localFiberIntoH (f * g⁻¹) * localFiberIntoH g at hh
  rw [map_mul, map_inv] at hh
  simp only [mul_assoc, inv_mul_cancel, mul_one] at hh
  by_cases hq1 : q = 1
  · left
    simpa only [hq1, map_one, one_mul] using hh.symm
  · right
    rw [qCentralInvolution_eq_of_mem_center_ne_one q hqc hq1] at hh
    exact hh.symm

/-- Forward triality sends central Q to the actual local element central times Omega. -/
theorem generatedTwelfth_forward_triality_central_local :
    sExtra * rhoLocal (inclQ qCentralInvolution) * sExtra⁻¹ =
      rhoLocal (inclQ (qCentralInvolution * sourceOmegaQ)) := by
  have hh : rhoLocal (inclQ (qCentralInvolution * sourceOmegaQ)) = trialityCentralSign 1 := by
    rw [map_mul, map_mul]
    change localCentralGriess * rhoLocal (inclQ sourceOmegaQ) = _
    rw [localCentralGriess_eq_trialityCentralSign, sourceOmegaQ_eq_trialityCentralSign,
      ← trialityCentralSign_zero_mul_one, ← mul_assoc, trialityCentralSign_square, one_mul]
  rw [hh]
  exact localCentralGriess_conjugate

/-- Entire triality images of fibers with identical full-Q action lie in the same H orbit. -/
theorem generatedTwelfth_full_Q_triality_local_orbit (f g : localFiberSubgroup)
    (he : spinConjugation f.val.1 = spinConjugation g.val.1) (x : GriessSpace) :
    ∃ h : H, sExtra (rhoLocal (localFiberIntoH f) x) =
      rhoLocal h (sExtra (rhoLocal (localFiberIntoH g) x)) := by
  rcases generatedTwelfth_full_Q_fiber_central_difference f g he with hh | hh
  · refine ⟨1, ?_⟩
    rw [hh, map_one]
    rfl
  · refine ⟨inclQ (qCentralInvolution * sourceOmegaQ), ?_⟩
    rw [hh, map_mul, LinearEquiv.mul_apply]
    rw [← generatedTwelfth_forward_triality_central_local]
    simp only [LinearEquiv.mul_apply, LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
