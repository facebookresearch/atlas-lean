/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleSecondaryActualTransitionCounts
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisOddStabilizerExact
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingOctadSourceTransport

/-! Genuine transport of the odd destination and fixed root to the original odd source. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The genuine incident minus-pair root on coordinates one and two. -/
def generatedFeasibleOddDestinationPair : Fin 276 := griessPairIndex 1 2 (by decide)

/-- The incident root address is bound to its actual physical coordinates. -/
theorem generatedFeasibleOddDestinationPair_coordinates :
    griessCoordinatePair generatedFeasibleOddDestinationPair = (1, 2) := by
  rw [generatedFeasibleOddDestinationPair, griessPairIndex_coordinates]
  rfl

private theorem source_word :
    ∃ p : golayAutomorphismSubgroup, p.val 0 = 1 ∧ p.val 1 = 2 ∧ p.val 2 = 0 := by
  let a : Fin 3 → Fin 24 := ![0, 1, 2]
  let b : Fin 3 → Fin 24 := ![1, 2, 0]
  have ha : Function.Injective a := by decide +kernel
  have hb : Function.Injective b := by decide +kernel
  obtain ⟨p, hp⟩ := leechRootedA2_three_transitive a b ha hb
  exact ⟨p, hp 0, hp 1, hp 2⟩

/-- An original Mathieu word transports the first root and actual odd prototype together. -/
theorem generatedFeasibleOddDestination_source_monomial :
    ∃ e : leechIsomSubgroup, e ∈ golayMonomialSubgroup ∧
      griessShortPermutation e (Sum.inl (0, generatedFeasiblePhysicalRootPair)) =
        Sum.inl (0, generatedFeasibleOddDestinationPair) ∧
      griessShortPermutation e generatedFeasibleSecondaryOddPrototypeLabel =
        Sum.inr (Sum.inr (0, 0)) := by
  obtain ⟨p, hp0, hp1, hp2⟩ := source_word
  let e := golayPermutationIsometry p
  have hz : golaySignIsometry 0 = 1 := golaySignHom.map_one
  refine ⟨e, ⟨0, p, by simp [e, hz]⟩, ?_, ?_⟩
  · apply (leechRootedA2_short_perm_eq_iff _ _ _).mpr
    left
    apply Subtype.ext
    rw [leechIntegralAction_golayPermutation]
    funext i
    have h0 : p.val.symm i = 0 ↔ i = 1 := by rw [Equiv.symm_apply_eq, hp0]
    have h1 : p.val.symm i = 1 ↔ i = 2 := by rw [Equiv.symm_apply_eq, hp1]
    simp only [golayIntegerPermute, griessShortLatticeVector, griessShortIntegral,
      generatedFeasiblePhysicalRootPair_coordinates,
      generatedFeasibleOddDestinationPair_coordinates, h0, h1, ite_true]
  · apply (leechRootedA2_short_perm_eq_iff _ _ _).mpr
    left
    apply Subtype.ext
    rw [leechIntegralAction_golayPermutation]
    funext i
    have h2 : p.val.symm i = 2 ↔ i = 0 := by rw [Equiv.symm_apply_eq, hp2]
    have hm : golayEncodedMask 0 = 0 := by decide +kernel
    simp only [golayIntegerPermute, griessShortLatticeVector, griessShortIntegral,
      generatedFeasibleSecondaryOddPrototypeLabel, Fin.val_zero, hm, Nat.zero_testBit,
      Bool.false_eq_true, ite_false, one_mul, h2]

private theorem incident_mate_base :
    toAdd (griessShortQ (Sum.inl (1, generatedFeasibleOddDestinationPair))).base =
      toAdd sourceOmegaQ.base +
        toAdd (griessShortQ (Sum.inl (0, generatedFeasibleOddDestinationPair))).base := by
  have hv : griessShortLatticeVector (Sum.inl (1, generatedFeasibleOddDestinationPair)) =
      leechCoordinateFrameLattice 1 -
        griessShortLatticeVector (Sum.inl (0, generatedFeasibleOddDestinationPair)) := by
    apply Subtype.ext
    funext i
    simp only [griessShortLatticeVector, griessShortIntegral,
      generatedFeasibleOddDestinationPair_coordinates, leechCoordinateFrameLattice,
      leechCoordinateFrameVector, Submodule.coe_sub, Pi.sub_apply]
    by_cases h1 : i = 1 <;> by_cases h2 : i = 2 <;> simp_all
  have hs : griessShortClass (Sum.inl (1, generatedFeasibleOddDestinationPair)) =
      leechReduction (leechCoordinateFrameLattice 0) +
        griessShortClass (Sum.inl (0, generatedFeasibleOddDestinationPair)) := by
    unfold griessShortClass
    rw [hv, map_sub, sub_eq_add_neg, ← map_neg, leechReduction_neg, leechFrame_reduction_eq]
  change leechHyperbolicCoordinates (griessShortClass _) =
    toAdd sourceOmegaQ.base + leechHyperbolicCoordinates (griessShortClass _)
  rw [hs, map_add]
  have hΩ : toAdd sourceOmegaQ.base =
      leechHyperbolicCoordinates (leechReduction (leechCoordinateFrameLattice 0)) :=
    sourceOmegaQ_eq_frame_class
  rw [hΩ]

private theorem incident_octad_independent :
    (griessShortQ (Sum.inr (Sum.inr (0, 0)))).base ≠
        (griessShortQ (Sum.inl (0, generatedFeasibleOddDestinationPair))).base ∧
      toAdd (griessShortQ (Sum.inr (Sum.inr (0, 0)))).base ≠
        toAdd sourceOmegaQ.base +
          toAdd (griessShortQ (Sum.inl (0, generatedFeasibleOddDestinationPair))).base := by
  constructor
  · intro he
    have hi := generatedFeasible_short_base_injective he
    cases hi
  · intro he
    rw [← incident_mate_base] at he
    have hi := generatedFeasible_short_base_injective (toAdd.injective he)
    cases hi

private theorem source_signed_transport :
    ∃ h : localOmegaStabilizer,
      rhoLocal h.val (conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 0) =
        conwayShortAxis (Sum.inl (0, generatedFeasibleOddDestinationPair)) 0 ∧
      rhoLocal h.val (conwayShortAxis generatedFeasibleSecondaryOddPrototypeLabel 0) =
        conwayShortAxis (Sum.inr (Sum.inr (0, 0))) 0 := by
  obtain ⟨e, he, hfirst, hoctad⟩ := generatedFeasibleOddDestination_source_monomial
  let a : co1OmegaFrameStabilizer :=
    ⟨QuotientGroup.mk e, generatedAxis_monomial_fixes_omega e he⟩
  obtain ⟨h, hh⟩ := localOmegaProjection_surjective a
  have hproj : projH h.val = QuotientGroup.mk e := congrArg Subtype.val hh
  obtain ⟨f, hf⟩ := QuotientGroup.mk'_surjective localDiagonalSubgroup h.val
  change localFiberIntoH f = h.val at hf
  have hfc : projH (localFiberIntoH f) = QuotientGroup.mk e :=
    (congrArg projH hf).trans hproj
  have hl (r : GriessShortIndex) :
      griessShortPermutation f.val.2 r = griessShortPermutation e r := by
    have hc : co1ShortPermutation (projH (localFiberIntoH f)) =
        griessShortPermutation f.val.2 := co1ShortPermutation_mk f.val.2
    rw [← hc, hfc, co1ShortPermutation_mk]
  have hlf := (hl (Sum.inl (0, generatedFeasiblePhysicalRootPair))).trans hfirst
  obtain ⟨q, hqΩ, hphase⟩ := generatedAxis_short_localOmega_phase
    (Sum.inl (0, generatedFeasibleOddDestinationPair))
    (localShortPhase f (Sum.inl (0, generatedFeasiblePhysicalRootPair)))
  let f' := localFiberIncl q * f
  have hzero : localShortPhase f' (Sum.inl (0, generatedFeasiblePhysicalRootPair)) = 0 := by
    rw [localShortPhase_mul, hlf, hphase]
    exact CharTwo.add_self_eq_zero _
  have hfp : griessShortPermutation f'.val.2 (Sum.inl (0, generatedFeasiblePhysicalRootPair)) =
      Sum.inl (0, generatedFeasibleOddDestinationPair) := by
    change griessShortPermutation (1 * f.val.2) _ = _
    simpa only [one_mul] using hlf
  have hfo : griessShortPermutation f'.val.2 generatedFeasibleSecondaryOddPrototypeLabel =
      (Sum.inr (Sum.inr (0, 0))) := by
    change griessShortPermutation (1 * f.val.2) _ = _
    simpa only [one_mul] using (hl _).trans hoctad
  have hΩ : localFiberIntoH f' ∈ localOmegaStabilizer := by
    change inclQ q * localFiberIntoH f ∈ localOmegaStabilizer
    rw [hf]
    exact localOmegaStabilizer.mul_mem hqΩ h.property
  have hr : rhoLocal (localFiberIntoH f')
      (conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 0) =
        conwayShortAxis (Sum.inl (0, generatedFeasibleOddDestinationPair)) 0 := by
    change localGriessRepresentation f' _ = _
    rw [generatedAxis_localFiber_image, hfp, hzero, add_zero]
  have ho : rhoLocal (localFiberIntoH f')
      (conwayShortAxis generatedFeasibleSecondaryOddPrototypeLabel 0) =
        conwayShortAxis (Sum.inr (Sum.inr (0, 0)))
          (localShortPhase f' generatedFeasibleSecondaryOddPrototypeLabel) := by
    change localGriessRepresentation f' _ = _
    rw [generatedAxis_localFiber_image, hfo, add_zero]
  obtain ⟨k, hk⟩ := generatedFeasible_independent_short_signed
    generatedFeasibleOddDestinationPair (Sum.inr (Sum.inr (0, 0)))
    incident_octad_independent.1 incident_octad_independent.2
    (localShortPhase f' generatedFeasibleSecondaryOddPrototypeLabel) 0
  refine ⟨⟨k.val * localFiberIntoH f',
    localOmegaStabilizer.mul_mem k.property.2 hΩ⟩, ?_, ?_⟩
  · rw [rhoLocal.map_mul, LinearEquiv.mul_apply, hr]
    exact localAxisStabilizer_signedAxis_fixed k.val _ k.property.1 0
  · rw [rhoLocal.map_mul, LinearEquiv.mul_apply, ho]
    exact hk

/-- One genuine local word transports both the fixed positive root and odd destination
to the orthogonal root and the original globally counted odd axis. -/
theorem generatedFeasibleOddDestination_source_transport :
    ∃ h : H,
      rhoLocal h (conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 0) =
        conwayShortAxis (Sum.inl (0, generatedFeasibleOddDestinationPair)) 0 ∧
      rhoLocal h generatedFeasibleSecondaryOddDestination = generatedOddAxis := by
  obtain ⟨n, hnfirst, hnoctad⟩ := source_signed_transport
  obtain ⟨h, hk⟩ := localOmegaStabilizer_triality_conjugate n
  have hw : extraIntoGenerated * localIntoGenerated n.val =
      localIntoGenerated h.val * extraIntoGenerated := by
    calc
      _ = (extraIntoGenerated * localIntoGenerated n.val * extraIntoGenerated⁻¹) *
          extraIntoGenerated := by group
      _ = _ := by rw [hk]
  have hh (x : GriessSpace) : rhoLocal h.val (sExtra x) = sExtra (rhoLocal n.val x) := by
    have he := congrArg (fun g : G => g.val x) hw
    exact he.symm
  refine ⟨h.val, ?_, ?_⟩
  · have he := hh (conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 0)
    rw [hnfirst, generatedAxis_triality_pair_exact, generatedAxis_triality_pair_exact] at he
    exact he
  · change rhoLocal h.val
      (sExtra (conwayShortAxis generatedFeasibleSecondaryOddPrototypeLabel 0)) =
      sExtra (conwayShortAxis (Sum.inr (Sum.inr (0, 0))) 0)
    rw [hh, hnoctad]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
