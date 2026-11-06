/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionBinary
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedNormalTrialityReflection

/-! Recovering the central sign suppressed by the binary orbit certificate.
The actual singleton cocode flips Ω and inverts triality, which is why the
source certificate checks both powers of triality on each binary root. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The actual singleton cocode has odd Ω conjugation phase. -/
theorem generatedAxisGlobal_singleton_omega_phase :
    qBeta (toAdd singletonCocodeQ.base) (toAdd sourceOmegaQ.base) +
      qBeta (toAdd sourceOmegaQ.base) (toAdd singletonCocodeQ.base) = 1 := by
  decide +kernel

/-- The genuine source singleton flips the full Ω element by the central involution. -/
theorem generatedAxisGlobal_singleton_omega_conjugate :
    singletonCocodeQ * sourceOmegaQ * singletonCocodeQ⁻¹ = qCentral 1 * sourceOmegaQ := by
  rw [q_conjugation_central_phase, generatedAxisGlobal_singleton_omega_phase]

/-- Every actual local element fixing the binary Ω class lies in one of the
two full-Ω cosets. The central phase is resolved by the actual singleton. -/
theorem generatedAxisGlobal_binary_normalizer_split (h : H)
    (hh : projH h ∈ co1OmegaFrameStabilizer) :
    h ∈ localOmegaStabilizer ∨ h * inclQ singletonCocodeQ ∈ localOmegaStabilizer := by
  obtain ⟨f, hf⟩ := QuotientGroup.mk'_surjective localDiagonalSubgroup h
  change localFiberIntoH f = h at hf
  have hb : (spinConjugation f.val.1 sourceOmegaQ).base = sourceOmegaQ.base := by
    apply toAdd.injective
    have ha := qBinaryAction_apply (spinConjugation f.val.1) sourceOmegaQ
    change spinBinaryAction f.val.1 (toAdd (qQuotHom sourceOmegaQ)) = _ at ha
    rw [f.property] at ha
    have hc : co1BinaryAction (projH h) (toAdd (qQuotHom sourceOmegaQ)) =
        toAdd (qQuotHom sourceOmegaQ) := hh
    rw [← hf] at hc
    exact ha.symm.trans hc
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
  have hbit := (by decide : ∀ d : ZMod 2, d = 0 ∨ d = 1) δ
  rcases hbit with hd | hd
  · left
    rw [← hf]
    apply (localOmegaStabilizer_fiber_iff _).mpr
    rw [hi, hd]
    change (1 : Q) * sourceOmegaQ = sourceOmegaQ
    rw [one_mul]
  · right
    rw [← hf]
    change localFiberIntoH (f * localFiberIncl singletonCocodeQ) ∈ localOmegaStabilizer
    apply (localOmegaStabilizer_fiber_iff _).mpr
    change spinConjugation (f.val.1 * spinHolomorphIncl singletonCocodeQ) sourceOmegaQ = _
    rw [map_mul]
    change spinConjugation f.val.1
      (spinConjugation (spinHolomorphIncl singletonCocodeQ) sourceOmegaQ) = _
    rw [spinConjugation_incl, generatedAxisGlobal_singleton_omega_conjugate,
      map_mul, spinConjugation_central, hi, hd]
    apply NormalizedCocycleExtension.Extension.ext
    · rw [qCentral_mul_base, qCentral_mul_base]
    · apply toAdd.injective
      rw [qCentral_mul_coeff, qCentral_mul_coeff]
      change (1 : ZMod 2) + (1 + toAdd sourceOmegaQ.coeff) = toAdd sourceOmegaQ.coeff
      rw [← add_assoc, ZModModule.add_self, zero_add]

/-- Binary-normalizer decompositions yield genuine full-Ω decompositions by
doubling the representative list with the source singleton. -/
theorem generatedAxisGlobal_decompose_two_signs {κ : Type*}
    (C : Subgroup H) (r : κ → H)
    (hcover : ∀ h : H, ∃ j n c,
      projH n ∈ co1OmegaFrameStabilizer ∧ c ∈ C ∧ h = n * r j * c)
    (h : H) :
    ∃ j n c, n ∈ localOmegaStabilizer ∧ c ∈ C ∧
      (h = n * r j * c ∨ h = n * (inclQ singletonCocodeQ * r j) * c) := by
  obtain ⟨j, n, c, hn, hc, he⟩ := hcover h
  rcases generatedAxisGlobal_binary_normalizer_split n hn with h0 | h1
  · exact ⟨j, n, c, h0, hc, Or.inl he⟩
  · refine ⟨j, n * inclQ singletonCocodeQ, c, h1, hc, Or.inr ?_⟩
    have hs : inclQ singletonCocodeQ * inclQ singletonCocodeQ = (1 : H) := by
      rw [← map_mul]
      change inclQ (cocodeQ _ * cocodeQ _) = 1
      rw [cocodeQ_square, map_one]
    rw [he]
    calc
      n * r j * c = n * (inclQ singletonCocodeQ * inclQ singletonCocodeQ) * r j * c := by
        rw [hs, mul_one]
      _ = _ := by group

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
