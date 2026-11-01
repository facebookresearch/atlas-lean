/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationEighthQMiddleFull
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisTransitionPairLift
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedForwardQLocal

/-! The actual fixing odd modulation resolves the full omega phase of any middle monomial fixer. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The genuine fixing pure modulation flips the full omega element, including its central phase. -/
theorem generatedEighth_middle_modulation_omega_flip :
    spinConjugation (spinHolomorphIncl (cocodeQ (golayLabelCoefficients 3079))) sourceOmegaQ =
      qCentral 1 * sourceOmegaQ := by
  rw [spinConjugation_incl, q_conjugation_central_phase]
  have hp : qBeta (toAdd (cocodeQ (golayLabelCoefficients 3079)).base)
      (toAdd sourceOmegaQ.base) +
      qBeta (toAdd sourceOmegaQ.base) (toAdd (cocodeQ (golayLabelCoefficients 3079)).base) = 1 := by
    decide +kernel
  rw [hp]

/-- A full middle monomial fixer admits a full-omega correction with unchanged spatial map. -/
theorem generatedEighth_middle_monomial_omega_correct (f : localFiberSubgroup)
    (hm : f.val.2 ∈ golayMonomialSubgroup)
    (hf : rhoLocal (localFiberIntoH f) generatedEighthMiddleAxis = generatedEighthMiddleAxis) :
    ∃ k : localFiberSubgroup, k.val.2 = f.val.2 ∧
      rhoLocal (localFiberIntoH k) generatedEighthMiddleAxis = generatedEighthMiddleAxis ∧
      spinConjugation k.val.1 sourceOmegaQ = sourceOmegaQ := by
  have hb : (spinConjugation f.val.1 sourceOmegaQ).base = sourceOmegaQ.base := by
    apply toAdd.injective
    have ha := qBinaryAction_apply (spinConjugation f.val.1) sourceOmegaQ
    change spinBinaryAction f.val.1 (toAdd (qQuotHom sourceOmegaQ)) = _ at ha
    rw [f.property] at ha
    exact ha.symm.trans (generatedAxis_monomial_fixes_omega f.val.2 hm)
  let δ : ZMod 2 := toAdd (spinConjugation f.val.1 sourceOmegaQ).coeff +
    toAdd sourceOmegaQ.coeff
  have hi : spinConjugation f.val.1 sourceOmegaQ = qCentral δ * sourceOmegaQ := by
    apply NormalizedCocycleExtension.Extension.ext
    · rw [qCentral_mul_base]
      exact hb
    · apply toAdd.injective
      rw [qCentral_mul_coeff]
      change _ = δ + toAdd sourceOmegaQ.coeff
      simp only [δ, add_assoc, ZModModule.add_self, add_zero]
  have hbit : δ = 0 ∨ δ = 1 :=
    (by decide +kernel : ∀ d : ZMod 2, d = 0 ∨ d = 1) δ
  rcases hbit with hd | hd
  · refine ⟨f, rfl, hf, ?_⟩
    rw [hi, hd]
    change (1 : Q) * sourceOmegaQ = sourceOmegaQ
    rw [one_mul]
  · let k := localFiberIncl (cocodeQ (golayLabelCoefficients 3079)) * f
    refine ⟨k, ?_, ?_, ?_⟩
    · change (1 : leechIsomSubgroup) * f.val.2 = f.val.2
      rw [one_mul]
    · change rhoLocal (inclQ (cocodeQ (golayLabelCoefficients 3079)) * localFiberIntoH f)
        generatedEighthMiddleAxis = generatedEighthMiddleAxis
      simp only [map_mul, LinearEquiv.mul_apply, hf,
        generatedEighth_middle_odd_modulation_full_fixed]
    · change spinConjugation (spinHolomorphIncl (cocodeQ (golayLabelCoefficients 3079)) *
        f.val.1) sourceOmegaQ = sourceOmegaQ
      rw [map_mul]
      change spinConjugation (spinHolomorphIncl (cocodeQ (golayLabelCoefficients 3079)))
        (spinConjugation f.val.1 sourceOmegaQ) = _
      rw [hi, hd, map_mul, spinConjugation_central, generatedEighth_middle_modulation_omega_flip]
      apply NormalizedCocycleExtension.Extension.ext
      · rw [qCentral_mul_base, qCentral_mul_base]
      · apply toAdd.injective
        rw [qCentral_mul_coeff, qCentral_mul_coeff]
        change (1 : ZMod 2) + (1 + toAdd sourceOmegaQ.coeff) = toAdd sourceOmegaQ.coeff
        rw [← add_assoc, ZModModule.add_self, zero_add]

/-- A full-omega middle fixer transports to a genuine complete final-axis local fixer. -/
theorem generatedEighth_middle_omega_forward_lift (f : localFiberSubgroup)
    (hf : rhoLocal (localFiberIntoH f) generatedEighthMiddleAxis = generatedEighthMiddleAxis)
    (ho : spinConjugation f.val.1 sourceOmegaQ = sourceOmegaQ) :
    ∃ h : H, rhoLocal h = sExtra * rhoLocal (localFiberIntoH f) * sExtra⁻¹ ∧
      rhoLocal h generatedEighthAxis = generatedEighthAxis := by
  have hfOmega := (localOmegaStabilizer_fiber_iff f).mpr ho
  have hc : localIntoGenerated (localFiberIntoH f) ∈ generatedAxisTransitionNormalizer := by
    rw [generatedAxisTransitionNormalizer_eq_local_omega]
    refine ⟨⟨localFiberIntoH f, rfl⟩, ?_⟩
    change localFiberIntoH f ∈ Subgroup.centralizer {inclQ sourceOmegaQ} at hfOmega
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    rw [Subgroup.mem_centralizer_singleton_iff] at hfOmega
    change localIntoGenerated (localFiberIntoH f) * localIntoGenerated (inclQ sourceOmegaQ) =
      localIntoGenerated (inclQ sourceOmegaQ) * localIntoGenerated (localFiberIntoH f)
    rw [← map_mul, ← map_mul, hfOmega]
  have ht := generatedAxisTransitionNormalizer_triality _ hc
  rw [generatedAxisTransitionNormalizer_eq_local_omega] at ht
  obtain ⟨h, hh⟩ := ht.1
  have ha : rhoLocal h = sExtra * rhoLocal (localFiberIntoH f) * sExtra⁻¹ :=
    congrArg Subtype.val hh
  refine ⟨h, ha, ?_⟩
  rw [ha, generatedEighthAxis_local_expression]
  change (sExtra * rhoLocal (localFiberIntoH f) * sExtra⁻¹)
    (sExtra generatedEighthMiddleAxis) = sExtra generatedEighthMiddleAxis
  simp only [LinearEquiv.mul_apply]
  change sExtra (rhoLocal (localFiberIntoH f)
    (sExtra.symm (sExtra generatedEighthMiddleAxis))) = _
  rw [LinearEquiv.symm_apply_apply, hf]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
