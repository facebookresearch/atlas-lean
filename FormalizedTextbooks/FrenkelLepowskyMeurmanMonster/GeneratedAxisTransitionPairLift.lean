/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisTransitionPairMonomial
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisTransitionPairPhase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisTransitionOmegaExact
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisEnumerationLocalCoordinates

/-! Actual signed-pair transitivity inside the genuine local Ω centralizer. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
open Multiplicative

/-- Every actual monomial isometry fixes the actual binary Ω class. -/
theorem generatedAxis_monomial_fixes_omega (e : leechIsomSubgroup)
    (he : e ∈ golayMonomialSubgroup) :
    leechBinaryAction e (toAdd (qQuotHom sourceOmegaQ)) = toAdd (qQuotHom sourceOmegaQ) := by
  have hf : e • leechReduction (leechCoordinateFrameLattice 0) =
      leechReduction (leechCoordinateFrameLattice 0) := by
    rw [← leechFrameClass_stabilizer_eq_monomial] at he
    exact he
  rw [sourceOmegaQ_eq_frame_class, leechBinaryAction_coordinates]
  exact congrArg leechHyperbolicCoordinates hf

/-- All 1104 actual signed pair axes lie in a single actual local Ω-centralizer orbit. -/
theorem generatedAxis_pair_localOmega_transitive (s t : Fin 2) (p q : Fin 276)
    (c d : ZMod 2) :
    ∃ h : localOmegaStabilizer,
      rhoLocal h.val (conwayShortAxis (Sum.inl (s, p)) c) =
        conwayShortAxis (Sum.inl (t, q)) d := by
  obtain ⟨e, he, hlabel⟩ := generatedAxis_pair_monomial_transitive s t p q
  let a : co1OmegaFrameStabilizer :=
    ⟨QuotientGroup.mk e, generatedAxis_monomial_fixes_omega e he⟩
  obtain ⟨h, hh⟩ := localOmegaProjection_surjective a
  have hproj : projH h.val = QuotientGroup.mk e := congrArg Subtype.val hh
  obtain ⟨f, hf⟩ := QuotientGroup.mk'_surjective localDiagonalSubgroup h.val
  change localFiberIntoH f = h.val at hf
  have hfc : projH (localFiberIntoH f) = QuotientGroup.mk e :=
    (congrArg projH hf).trans hproj
  have hp : griessShortPermutation f.val.2 (Sum.inl (s, p)) = Sum.inl (t, q) := by
    have hco : co1ShortPermutation (projH (localFiberIntoH f)) =
        griessShortPermutation f.val.2 := co1ShortPermutation_mk f.val.2
    rw [← hco, hfc, co1ShortPermutation_mk]
    exact hlabel
  obtain ⟨v, hv, hphase⟩ := generatedAxis_pair_localOmega_phase t q
    (d + localShortPhase f (Sum.inl (s, p)) + c)
  have hsum : localShortPhase (localFiberIncl v * f) (Sum.inl (s, p)) + c = d := by
    rw [localShortPhase_mul, hp, hphase]
    have hbit : ∀ x : ZMod 2, x + x = 0 := CharTwo.add_self_eq_zero
    linear_combination hbit (localShortPhase f (Sum.inl (s, p))) + hbit c
  have hmem : localFiberIntoH (localFiberIncl v * f) ∈ localOmegaStabilizer := by
    change inclQ v * localFiberIntoH f ∈ localOmegaStabilizer
    rw [hf]
    exact localOmegaStabilizer.mul_mem hv h.property
  refine ⟨⟨localFiberIntoH (localFiberIncl v * f), hmem⟩, ?_⟩
  change localGriessRepresentation (localFiberIncl v * f) _ = _
  rw [generatedAxis_localFiber_image, hsum]
  have hl : griessShortPermutation (localFiberIncl v * f).val.2 (Sum.inl (s, p)) =
      Sum.inl (t, q) := by
    change griessShortPermutation (1 * f.val.2) _ = _
    simpa only [one_mul] using hp
  rw [hl]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
