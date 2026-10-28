/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationPhaseSeparation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisTransitionPairLift

/-! Arbitrary short-axis sign correction within the actual Ω centralizer. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- Nondegeneracy of the genuine extraspecial commutator makes the binary
phase-character parameter faithful. -/
theorem generatedAxis_binary_phase_injective : Function.Injective localAxisBinaryPhase := by
  intro u v he
  let g : Q := ⟨ofAdd (u + v), 1⟩
  have hc : g ∈ centerQ := by
    apply Subgroup.mem_center_iff.mpr
    intro q
    symm
    apply (q_mul_comm_iff g q).mpr
    have h := congrArg (fun χ : Q →* Multiplicative (ZMod 2) => toAdd (χ q)) he
    change qBeta (toAdd q.base) u + qBeta u (toAdd q.base) =
      qBeta (toAdd q.base) v + qBeta v (toAdd q.base) at h
    change qBeta (u + v) (toAdd q.base) = qBeta (toAdd q.base) (u + v)
    rw [qBeta_add_left, qBeta_add_right]
    linear_combination h + CharTwo.add_self_eq_zero (qBeta v (toAdd q.base)) -
      CharTwo.add_self_eq_zero (qBeta (toAdd q.base) u)
  have hb := (q_mem_center_iff_base_eq_one g).mp hc
  have hs : u + v = 0 := congrArg toAdd hb
  have hn : -v = v := by funext i; exact CharTwo.neg_eq (v i)
  exact (eq_neg_of_add_eq_zero_left hs).trans hn

/-- Either sign on every actual short axis can be prescribed while fixing Ω. -/
theorem generatedAxis_short_localOmega_phase (r : GriessShortIndex) (δ : ZMod 2) :
    ∃ q : Q, inclQ q ∈ localOmegaStabilizer ∧
      localShortPhase (localFiberIncl q) r = δ := by
  have hne : localAxisQPhase r ≠ localOmegaQPhase := by
    intro h
    have hb := generatedAxis_binary_phase_injective h
    exact generatedAxis_short_base_ne_omega r (toAdd.injective hb)
  obtain ⟨q, hΩ, hr⟩ := generatedAxis_binary_characters_kernel
    localOmegaQPhase (localAxisQPhase r) localOmegaQPhase_surjective
    (localAxisQPhase_surjective r) hne
  have hmem : inclQ q ∈ localOmegaStabilizer := by
    have hc : q ∈ Subgroup.centralizer {sourceOmegaQ} := by
      rw [← localOmegaQPhase_kernel_eq_centralizer]
      exact hΩ
    rw [localOmegaStabilizer, Subgroup.mem_centralizer_singleton_iff,
      ← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.mp hc]
  have hphase : localShortPhase (localFiberIncl q) r = 1 := by
    rw [localAxisQPhase_eq_short_phase, hr]
    rfl
  have hbit : δ = 0 ∨ δ = 1 := by fin_cases δ <;> simp
  rcases hbit with rfl | rfl
  · refine ⟨1, ?_, ?_⟩
    · simpa only [map_one] using localOmegaStabilizer.one_mem
    · rw [localAxisQPhase_eq_short_phase, map_one]
      rfl
  · exact ⟨q, hmem, hphase⟩

/-- Every actual monomial label transport lifts to signed-axis transport
inside the actual local Ω centralizer. -/
theorem generatedAxis_monomial_signed_localOmega (r s : GriessShortIndex)
    (e : leechIsomSubgroup) (he : e ∈ golayMonomialSubgroup)
    (hlabel : griessShortPermutation e r = s) (c d : ZMod 2) :
    ∃ h : localOmegaStabilizer, rhoLocal h.val (conwayShortAxis r c) = conwayShortAxis s d := by
  let a : co1OmegaFrameStabilizer :=
    ⟨QuotientGroup.mk e, generatedAxis_monomial_fixes_omega e he⟩
  obtain ⟨h, hh⟩ := localOmegaProjection_surjective a
  have hproj : projH h.val = QuotientGroup.mk e := congrArg Subtype.val hh
  obtain ⟨f, hf⟩ := QuotientGroup.mk'_surjective localDiagonalSubgroup h.val
  change localFiberIntoH f = h.val at hf
  have hfc : projH (localFiberIntoH f) = QuotientGroup.mk e :=
    (congrArg projH hf).trans hproj
  have hp : griessShortPermutation f.val.2 r = s := by
    have hco : co1ShortPermutation (projH (localFiberIntoH f)) =
        griessShortPermutation f.val.2 := co1ShortPermutation_mk f.val.2
    rw [← hco, hfc, co1ShortPermutation_mk]
    exact hlabel
  obtain ⟨v, hv, hphase⟩ := generatedAxis_short_localOmega_phase s
    (d + localShortPhase f r + c)
  have hsum : localShortPhase (localFiberIncl v * f) r + c = d := by
    rw [localShortPhase_mul, hp, hphase]
    have hbit : ∀ x : ZMod 2, x + x = 0 := CharTwo.add_self_eq_zero
    linear_combination hbit (localShortPhase f r) + hbit c
  have hmem : localFiberIntoH (localFiberIncl v * f) ∈ localOmegaStabilizer := by
    change inclQ v * localFiberIntoH f ∈ localOmegaStabilizer
    rw [hf]
    exact localOmegaStabilizer.mul_mem hv h.property
  refine ⟨⟨localFiberIntoH (localFiberIncl v * f), hmem⟩, ?_⟩
  change localGriessRepresentation (localFiberIncl v * f) _ = _
  rw [generatedAxis_localFiber_image, hsum]
  have hl : griessShortPermutation (localFiberIncl v * f).val.2 r = s := by
    change griessShortPermutation (1 * f.val.2) r = s
    simpa only [one_mul] using hp
  rw [hl]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
