/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisTransitionOmegaProjection

/-! Exact counting of the actual local Ω centralizer. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- A genuine Q phase correction makes every Ω-class stabilizer lift fix actual Ω. -/
theorem localOmegaProjection_surjective : Function.Surjective localOmegaProjection := by
  intro c
  obtain ⟨h, hh⟩ := projH_surjective c.val
  obtain ⟨f, hf⟩ := QuotientGroup.mk'_surjective localDiagonalSubgroup h
  change localFiberIntoH f = h at hf
  have hfc : projH (localFiberIntoH f) = c.val := (congrArg projH hf).trans hh
  have hp : leechBinaryAction f.val.2 (toAdd (qQuotHom sourceOmegaQ)) =
      toAdd (qQuotHom sourceOmegaQ) := by
    have hc : co1BinaryAction c.val (toAdd (qQuotHom sourceOmegaQ)) =
        toAdd (qQuotHom sourceOmegaQ) := c.property
    rw [← hfc] at hc
    exact hc
  have hb : (spinConjugation f.val.1 sourceOmegaQ).base = sourceOmegaQ.base := by
    apply toAdd.injective
    have ha := qBinaryAction_apply (spinConjugation f.val.1) sourceOmegaQ
    change spinBinaryAction f.val.1 (toAdd (qQuotHom sourceOmegaQ)) = _ at ha
    rw [f.property] at ha
    exact ha.symm.trans hp
  let δ : ZMod 2 := toAdd (spinConjugation f.val.1 sourceOmegaQ).coeff +
    toAdd sourceOmegaQ.coeff
  have himage : spinConjugation f.val.1 sourceOmegaQ = qCentral δ * sourceOmegaQ := by
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
  have hfixed : spinConjugation (localFiberIncl q * f).val.1 sourceOmegaQ = sourceOmegaQ := by
    change spinConjugation (spinHolomorphIncl q * f.val.1) sourceOmegaQ = sourceOmegaQ
    rw [map_mul]
    change spinConjugation (spinHolomorphIncl q) (spinConjugation f.val.1 sourceOmegaQ) = _
    rw [himage, map_mul, spinConjugation_central, spinConjugation_incl,
      q_conjugation_central_phase, hphase]
    apply NormalizedCocycleExtension.Extension.ext
    · rw [qCentral_mul_base, qCentral_mul_base]
    · apply toAdd.injective
      rw [qCentral_mul_coeff, qCentral_mul_coeff]
      change δ + (δ + toAdd sourceOmegaQ.coeff) = toAdd sourceOmegaQ.coeff
      rw [← add_assoc, ZModModule.add_self, zero_add]
  have hmem := (localOmegaStabilizer_fiber_iff (localFiberIncl q * f)).mpr hfixed
  refine ⟨⟨localFiberIntoH (localFiberIncl q * f), hmem⟩, Subtype.ext ?_⟩
  change projH (localFiberIntoH (localFiberIncl q * f)) = c.val
  change projH (inclQ q * localFiberIntoH f) = c.val
  rw [map_mul, projH_inclQ, one_mul, hfc]

/-- The actual Ω phase kernel embeds in the actual local Ω centralizer. -/
noncomputable def localOmegaPhaseInclusion : localOmegaQPhase.ker →* localOmegaStabilizer :=
  (inclQ.comp localOmegaQPhase.ker.subtype).codRestrict _ (by
    intro q
    change q.val ∈ localOmegaStabilizer.comap inclQ
    rw [localOmegaStabilizer_comap_inclQ]
    exact q.property)

/-- The genuine phase inclusion is injective. -/
theorem localOmegaPhaseInclusion_injective : Function.Injective localOmegaPhaseInclusion := by
  intro q k h
  apply Subtype.ext
  apply inclQ_injective
  exact congrArg Subtype.val h

/-- Exactness of the actual local Ω centralizer projection. -/
theorem localOmegaPhaseInclusion_range :
    localOmegaPhaseInclusion.range = localOmegaProjection.ker := by
  ext h
  constructor
  · rintro ⟨q, rfl⟩
    apply Subtype.ext
    exact projH_inclQ q.val
  · intro hker
    have hk : h.val ∈ projH.ker := congrArg Subtype.val hker
    rw [← inclQ_range_eq_projH_ker] at hk
    obtain ⟨q, hq⟩ := hk
    have hphase : q ∈ localOmegaQPhase.ker := by
      rw [← localOmegaStabilizer_comap_inclQ]
      change inclQ q ∈ localOmegaStabilizer
      rw [hq]
      exact h.property
    exact ⟨⟨q, hphase⟩, Subtype.ext hq⟩

/-- The actual Ω centralizer projection has kernel order 2²⁴. -/
theorem localOmegaProjection_kernel_card : Nat.card localOmegaProjection.ker = 2 ^ 24 := by
  rw [← localOmegaPhaseInclusion_range]
  have h := Nat.card_congr (MonoidHom.ofInjective localOmegaPhaseInclusion_injective).toEquiv
  rw [← h]
  exact localOmegaQPhase_kernel_card

/-- The actual local Ω centralizer has its proved exact-sequence order. -/
theorem localOmegaStabilizer_card :
    Nat.card localOmegaStabilizer = 2 ^ 24 * Nat.card co1OmegaFrameStabilizer := by
  have h := localOmegaProjection.ker.card_mul_index
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr localOmegaProjection_surjective,
    Subgroup.card_top, localOmegaProjection_kernel_card] at h
  exact h.symm

/-- The actual local Ω centralizer has precisely 16,584,750 cosets in H. -/
theorem localOmegaStabilizer_index : localOmegaStabilizer.index = 16584750 := by
  have h := localOmegaStabilizer.card_mul_index
  have hs : Nat.card localOmegaStabilizer = 8412055600858398720 := by
    rw [localOmegaStabilizer_card, co1OmegaFrameStabilizer_card]
    norm_num
  rw [hs, local_h_card_exact] at h
  exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 8412055600858398720) h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
