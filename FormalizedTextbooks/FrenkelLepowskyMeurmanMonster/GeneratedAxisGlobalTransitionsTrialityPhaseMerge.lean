/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalCoverageBinary

/-! An actual extraspecial stabilizer element with odd root pairing identifies
the two triality-sign orbits. Every phase is computed in the genuine Q model. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- An odd actual root pairing puts the corrected conjugate in the full Ω stabilizer. -/
theorem generatedAxisGlobal_root_phase_normalizer (r : H) (q : Q)
    (hphase : qBeta (toAdd q.base) (generatedAxisGlobalBinaryRoot r).val +
      qBeta (generatedAxisGlobalBinaryRoot r).val (toAdd q.base) = 1) :
    (r * inclQ q * r⁻¹) * inclQ singletonCocodeQ ∈ localOmegaStabilizer := by
  obtain ⟨f, hf⟩ := QuotientGroup.mk'_surjective localDiagonalSubgroup r
  change localFiberIntoH f = r at hf
  have hb := qBinaryAction_apply (spinConjugation (f⁻¹).val.1) sourceOmegaQ
  change spinBinaryAction (f⁻¹).val.1 (toAdd (qQuotHom sourceOmegaQ)) =
    toAdd (spinConjugation (f⁻¹).val.1 sourceOmegaQ).base at hb
  rw [(f⁻¹).property] at hb
  have hb' : (generatedAxisGlobalBinaryRoot r).val =
      toAdd (spinConjugation (f⁻¹).val.1 sourceOmegaQ).base := by
    rw [← hf]
    exact hb
  have hqp : q * spinConjugation (f⁻¹).val.1 sourceOmegaQ * q⁻¹ =
      qCentral 1 * spinConjugation (f⁻¹).val.1 sourceOmegaQ := by
    rw [q_conjugation_central_phase]
    rw [hb'] at hphase
    rw [hphase]
  change q * spinConjugation f.val.1⁻¹ sourceOmegaQ * q⁻¹ =
    qCentral 1 * spinConjugation f.val.1⁻¹ sourceOmegaQ at hqp
  have hg : spinConjugation (f * localFiberIncl q * f⁻¹).val.1 sourceOmegaQ =
      qCentral 1 * sourceOmegaQ := by
    change spinConjugation (f.val.1 * spinHolomorphIncl q * f.val.1⁻¹) sourceOmegaQ = _
    rw [map_mul, map_mul]
    change spinConjugation f.val.1
      (spinConjugation (spinHolomorphIncl q)
        (spinConjugation f.val.1⁻¹ sourceOmegaQ)) = _
    rw [spinConjugation_incl, hqp, map_mul, spinConjugation_central]
    rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  rw [← hf]
  change localFiberIntoH ((f * localFiberIncl q * f⁻¹) *
    localFiberIncl singletonCocodeQ) ∈ localOmegaStabilizer
  apply (localOmegaStabilizer_fiber_iff _).mpr
  change spinConjugation
    ((f * localFiberIncl q * f⁻¹).val.1 * spinHolomorphIncl singletonCocodeQ)
      sourceOmegaQ = sourceOmegaQ
  rw [map_mul]
  change spinConjugation (f * localFiberIncl q * f⁻¹).val.1
    (spinConjugation (spinHolomorphIncl singletonCocodeQ) sourceOmegaQ) = _
  rw [spinConjugation_incl, generatedAxisGlobal_singleton_omega_conjugate,
    map_mul, spinConjugation_central, hg]
  apply NormalizedCocycleExtension.Extension.ext
  · rw [qCentral_mul_base, qCentral_mul_base]
  · apply toAdd.injective
    rw [qCentral_mul_coeff, qCentral_mul_coeff]
    change (1 : ZMod 2) + (1 + toAdd sourceOmegaQ.coeff) = toAdd sourceOmegaQ.coeff
    rw [← add_assoc, ZModModule.add_self, zero_add]

/-- An actual Q fixer with odd root pairing identifies both full-vector triality-sign orbits. -/
theorem generatedAxisGlobal_triality_phase_merge (v : GriessSpace) (r : H) (q : Q)
    (hfix : rhoLocal (inclQ q) v = v)
    (hphase : qBeta (toAdd q.base) (generatedAxisGlobalBinaryRoot r).val +
      qBeta (generatedAxisGlobalBinaryRoot r).val (toAdd q.base) = 1) :
    ∃ k : H, sExtra (rhoLocal r v) = rhoLocal k (sExtra⁻¹ (rhoLocal r v)) := by
  have hn := generatedAxisGlobal_root_phase_normalizer r q hphase
  have hs : inclQ singletonCocodeQ * inclQ singletonCocodeQ = (1 : H) := by
    rw [← map_mul]
    change inclQ (cocodeQ _ * cocodeQ _) = 1
    rw [cocodeQ_square, map_one]
  have he : r * inclQ q = ((r * inclQ q * r⁻¹) * inclQ singletonCocodeQ) *
      (inclQ singletonCocodeQ * r) := by
    calc
      r * inclQ q = (r * inclQ q * r⁻¹) * r := by group
      _ = (r * inclQ q * r⁻¹) *
          (inclQ singletonCocodeQ * inclQ singletonCocodeQ) * r := by rw [hs, mul_one]
      _ = _ := by group
  obtain ⟨k, hk⟩ := localOmegaStabilizer_triality_orbit
    ⟨(r * inclQ q * r⁻¹) * inclQ singletonCocodeQ, hn⟩
    (rhoLocal (inclQ singletonCocodeQ * r) v)
  refine ⟨k * inclQ singletonCocodeQ, ?_⟩
  calc
    sExtra (rhoLocal r v) = sExtra (rhoLocal (r * inclQ q) v) := by
      rw [map_mul, LinearEquiv.mul_apply, hfix]
    _ = _ := by
      rw [he, map_mul, LinearEquiv.mul_apply, ← hk, map_mul, LinearEquiv.mul_apply,
        generatedAxisGlobal_singleton_triality_exchange, map_mul, LinearEquiv.mul_apply]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
