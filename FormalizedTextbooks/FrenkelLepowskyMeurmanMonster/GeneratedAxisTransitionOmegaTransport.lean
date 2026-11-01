/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisTransitionOmegaExact
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedCentralizerRecognition

/-! Phase-correct transport of actual Q elements to Ω and of their centralizers to H. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- An actual Conway binary transport lifts to conjugacy of the actual Q elements,
including their central signs. -/
theorem localOmega_conjugate_of_binary_transport (r : Q) (c : Co1)
    (hc : co1BinaryAction c (toAdd (qQuotHom r)) = toAdd (qQuotHom sourceOmegaQ)) :
    ∃ h : H, h * inclQ r * h⁻¹ = inclQ sourceOmegaQ := by
  obtain ⟨h, hh⟩ := projH_surjective c
  obtain ⟨f, hf⟩ := QuotientGroup.mk'_surjective localDiagonalSubgroup h
  change localFiberIntoH f = h at hf
  have hfc : projH (localFiberIntoH f) = c := (congrArg projH hf).trans hh
  have hp : leechBinaryAction f.val.2 (toAdd (qQuotHom r)) =
      toAdd (qQuotHom sourceOmegaQ) := by
    rw [← hfc] at hc
    exact hc
  have hb : (spinConjugation f.val.1 r).base = sourceOmegaQ.base := by
    apply toAdd.injective
    have ha := qBinaryAction_apply (spinConjugation f.val.1) r
    change spinBinaryAction f.val.1 (toAdd (qQuotHom r)) = _ at ha
    rw [f.property] at ha
    exact ha.symm.trans hp
  let δ : ZMod 2 := toAdd (spinConjugation f.val.1 r).coeff + toAdd sourceOmegaQ.coeff
  have himage : spinConjugation f.val.1 r = qCentral δ * sourceOmegaQ := by
    apply NormalizedCocycleExtension.Extension.ext
    · rw [qCentral_mul_base]
      exact hb
    · apply toAdd.injective
      rw [qCentral_mul_coeff]
      change _ = δ + toAdd sourceOmegaQ.coeff
      simp only [δ, add_assoc, ZModModule.add_self, add_zero]
  obtain ⟨q, hq⟩ := localOmegaQPhase_surjective (ofAdd δ)
  have hphase : qBeta (toAdd q.base) (toAdd sourceOmegaQ.base) +
      qBeta (toAdd sourceOmegaQ.base) (toAdd q.base) = δ := congrArg toAdd hq
  have hfixed : spinConjugation (localFiberIncl q * f).val.1 r = sourceOmegaQ := by
    change spinConjugation (spinHolomorphIncl q * f.val.1) r = sourceOmegaQ
    rw [map_mul]
    change spinConjugation (spinHolomorphIncl q) (spinConjugation f.val.1 r) = _
    rw [himage, map_mul, spinConjugation_central, spinConjugation_incl,
      q_conjugation_central_phase, hphase]
    apply NormalizedCocycleExtension.Extension.ext
    · rw [qCentral_mul_base, qCentral_mul_base]
    · apply toAdd.injective
      rw [qCentral_mul_coeff, qCentral_mul_coeff]
      change δ + (δ + toAdd sourceOmegaQ.coeff) = toAdd sourceOmegaQ.coeff
      rw [← add_assoc, ZModModule.add_self, zero_add]
  exact ⟨localFiberIntoH (localFiberIncl q * f),
    (inclQ_spinConjugation (localFiberIncl q * f) r).symm.trans (congrArg inclQ hfixed)⟩

/-- An element commuting with such an actual Q element has an explicit conjugate
in the actual local group. No trace or conjugacy-class label is assumed. -/
theorem generated_commuting_q_conjugate_local_of_binary_transport (r : Q) (c : Co1)
    (hc : co1BinaryAction c (toAdd (qQuotHom r)) = toAdd (qQuotHom sourceOmegaQ))
    (g : G) (hg : Commute g (qIntoGenerated r)) :
    ∃ h : H, extraIntoGenerated *
      (localIntoGenerated h * g * (localIntoGenerated h)⁻¹) * extraIntoGenerated⁻¹ ∈
        localIntoGenerated.range := by
  obtain ⟨h, hh⟩ := localOmega_conjugate_of_binary_transport r c hc
  have hhG : localIntoGenerated h * qIntoGenerated r * (localIntoGenerated h)⁻¹ =
      qIntoGenerated sourceOmegaQ := by
    change localIntoGenerated h * localIntoGenerated (inclQ r) *
      (localIntoGenerated h)⁻¹ = localIntoGenerated (inclQ sourceOmegaQ)
    simpa only [map_mul, map_inv] using congrArg localIntoGenerated hh
  have hcomm := (hg.conj (localIntoGenerated h)).conj extraIntoGenerated
  rw [hhG] at hcomm
  have hs : extraIntoGenerated * qIntoGenerated sourceOmegaQ * extraIntoGenerated⁻¹ =
      qIntoGenerated qCentralInvolution := by
    rw [qIntoGenerated_sourceOmegaQ]
    apply Subtype.ext
    change sExtra * trialityCentralSign 2 * sExtra⁻¹ = localCentralGriess
    rw [trialityCentralSign_conjugate]
    change trialityCentralSign 0 = localCentralGriess
    exact localCentralGriess_eq_trialityCentralSign.symm
  rw [hs] at hcomm
  refine ⟨h, ?_⟩
  rw [← generatedCentralizer_eq_local_range]
  exact Subgroup.mem_centralizer_singleton_iff.mpr hcomm

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
