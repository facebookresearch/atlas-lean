/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingZeroOutsideAnchorFlagData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingZeroOutsideAnchorWholeAxis
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingEighthInputRecognition

/-! Entire actual endpoint transport retains the positive original first-axis flag. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

private theorem monomial_flag_lift (e : leechIsomSubgroup)
    (he : e ∈ golayMonomialSubgroup)
    (hp : griessShortPermutation e (Sum.inl (0, (23 : Fin 276))) =
      Sum.inl (0, generatedFeasiblePhysicalRootPair)) :
    ∃ f : localFiberSubgroup,
      localFiberIntoH f ∈ localOmegaStabilizer ∧
      (∀ r, griessShortPermutation f.val.2 r = griessShortPermutation e r) ∧
      rhoLocal (localFiberIntoH f) (conwayShortAxis (Sum.inl (0, (23 : Fin 276))) 0) =
        conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 0 := by
  let a : co1OmegaFrameStabilizer :=
    ⟨QuotientGroup.mk e, generatedAxis_monomial_fixes_omega e he⟩
  obtain ⟨h, hh⟩ := localOmegaProjection_surjective a
  have hproj : projH h.val = QuotientGroup.mk e := congrArg Subtype.val hh
  obtain ⟨f, hf⟩ := QuotientGroup.mk'_surjective localDiagonalSubgroup h.val
  change localFiberIntoH f = h.val at hf
  have hfc : projH (localFiberIntoH f) = QuotientGroup.mk e := (congrArg projH hf).trans hproj
  have hl (r : GriessShortIndex) : griessShortPermutation f.val.2 r = griessShortPermutation e r := by
    have hco : co1ShortPermutation (projH (localFiberIntoH f)) =
        griessShortPermutation f.val.2 := co1ShortPermutation_mk f.val.2
    rw [← hco, hfc, co1ShortPermutation_mk]
  have hp' := (hl (Sum.inl (0, (23 : Fin 276)))).trans hp
  obtain ⟨q, hqΩ, hphase⟩ := generatedAxis_pair_localOmega_phase 0 generatedFeasiblePhysicalRootPair
    (localShortPhase f (Sum.inl (0, (23 : Fin 276))))
  let F := localFiberIncl q * f
  have hFL (r : GriessShortIndex) :
      griessShortPermutation F.val.2 r = griessShortPermutation e r := by
    change griessShortPermutation (1 * f.val.2) r = _
    rw [one_mul]
    exact hl r
  have hFp : localShortPhase F (Sum.inl (0, (23 : Fin 276))) = 0 := by
    rw [localShortPhase_mul, hp', hphase]
    exact CharTwo.add_self_eq_zero _
  refine ⟨F, ?_, hFL, ?_⟩
  · change inclQ q * localFiberIntoH f ∈ localOmegaStabilizer
    rw [hf]
    exact localOmegaStabilizer.mul_mem hqΩ h.property
  · change localGriessRepresentation F _ = _
    rw [generatedAxis_localFiber_image, hFL, hp, hFp, zero_add]

private theorem triality_conjugate_commute (g : localOmegaStabilizer) :
    ∃ g' : localOmegaStabilizer,
      ∀ x : GriessSpace, rhoLocal g'.val (sExtra x) = sExtra (rhoLocal g.val x) := by
  obtain ⟨g', hg⟩ := localOmegaStabilizer_triality_conjugate g
  refine ⟨g', ?_⟩
  intro x
  have hw : extraIntoGenerated * localIntoGenerated g.val =
      localIntoGenerated g'.val * extraIntoGenerated := by
    calc
      _ = (extraIntoGenerated * localIntoGenerated g.val * extraIntoGenerated⁻¹) *
          extraIntoGenerated := by group
      _ = _ := by rw [hg]
  exact (congrArg (fun h : G => h.val x) hw).symm

private theorem normalize_flag (r s target : GriessShortIndex)
    (hs : ∀ c : ZMod 2,
      ∃ u : ↥(localAxisStabilizer generatedFeasiblePhysicalRootPair ⊓ localOmegaStabilizer),
        rhoLocal u.val (conwayShortAxis s c) = conwayShortAxis target 0)
    (hr : griessShortPermutation generatedFeasibleContainingZeroOutsideAnchorFlagIsometry r = s) :
    ∃ w : H,
      rhoLocal w (sExtra (conwayShortAxis r 0)) = sExtra (conwayShortAxis target 0) ∧
      rhoLocal w (conwayShortAxis (Sum.inl (0, (23 : Fin 276))) 0) =
        conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 0 := by
  obtain ⟨f, hfN, hfL, hfp⟩ := monomial_flag_lift
    generatedFeasibleContainingZeroOutsideAnchorFlagIsometry
    generatedFeasibleContainingZeroOutsideAnchorFlagIsometry_monomial
    generatedFeasibleContainingZeroOutsideAnchorFlagIsometry_first
  let g : localOmegaStabilizer := ⟨localFiberIntoH f, hfN⟩
  obtain ⟨g', hg⟩ := triality_conjugate_commute g
  let c := localShortPhase f r + 0
  have hshort : rhoLocal g.val (conwayShortAxis r 0) = conwayShortAxis s c := by
    change localGriessRepresentation f _ = _
    rw [generatedAxis_localFiber_image, hfL, hr]
  obtain ⟨u, hu⟩ := hs c
  let v : localOmegaStabilizer := ⟨u.val, u.property.2⟩
  obtain ⟨v', hv⟩ := triality_conjugate_commute v
  have hgp : rhoLocal g'.val (conwayShortAxis (Sum.inl (0, (23 : Fin 276))) 0) =
      conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 0 := by
    have h := hg (conwayShortAxis (Sum.inl (0, (23 : Fin 276))) 0)
    rw [generatedAxis_triality_pair_exact, hfp, generatedAxis_triality_pair_exact] at h
    exact h
  have hvp : rhoLocal v'.val (conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 0) =
      conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 0 := by
    have h := hv (conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 0)
    have hp : rhoLocal v.val (conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 0) =
        conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 0 := by
      rw [conwayShortAxis_pair_zero]
      exact u.property.1
    rw [generatedAxis_triality_pair_exact, hp, generatedAxis_triality_pair_exact] at h
    exact h
  refine ⟨v'.val * g'.val, ?_, ?_⟩
  · rw [map_mul, LinearEquiv.mul_apply, hg, hshort, hv, hu]
  · rw [map_mul, LinearEquiv.mul_apply, hgp, hvp]

/-- The entire existing outside class reaches the checked source while preserving its positive flag. -/
theorem generatedFeasibleContainingZeroOutsideAnchorOutside_source_flag :
    ∃ r : H, rhoLocal r generatedFeasibleOutsideOctadDestination =
        generatedFeasibleContainingZeroOutsideAnchorSource ∧
      rhoLocal r (conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 0) =
        conwayShortAxis (Sum.inl (0, (23 : Fin 276))) 0 := by
  obtain ⟨w, hw, hp⟩ := normalize_flag
    (Sum.inr (Sum.inl (generatedFeasibleContainingZeroOutsideAnchorOctad 10, 0)))
    (generatedFeasibleContainingZeroOutsideAnchorFlagLabel 0)
    generatedFeasibleOutsideOctadPrototypeLabel
    (fun c => generatedFeasibleOutsideOctad_to_prototype _
      generatedFeasibleContainingZeroOutsideAnchorOutside_mem c 0)
    (generatedFeasibleContainingZeroOutsideAnchorFlagIsometry_octad 0)
  refine ⟨w⁻¹, ?_, ?_⟩
  · exact generatedFeasibleContaining_inverse_transports _ _ _ hw
  · exact generatedFeasibleContaining_inverse_transports _ _ _ hp

/-- The entire containing class reaches the checked target while preserving its positive flag. -/
theorem generatedFeasibleContainingZeroOutsideAnchorContaining_source_flag :
    ∃ q : H, rhoLocal q generatedFeasibleContainingOctadDestination =
        generatedFeasibleContainingZeroOutsideAnchorTarget ∧
      rhoLocal q (conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 0) =
        conwayShortAxis (Sum.inl (0, (23 : Fin 276))) 0 := by
  obtain ⟨w, hw, hp⟩ := normalize_flag
    (Sum.inr (Sum.inl (generatedFeasibleContainingZeroOutsideAnchorOctad 6, 0)))
    (generatedFeasibleContainingZeroOutsideAnchorFlagLabel 1)
    generatedFeasibleContainingOctadPrototypeLabel
    (fun c => generatedFeasibleContainingOctad_to_prototype _
      generatedFeasibleContainingZeroOutsideAnchorContaining_mem c 0)
    (generatedFeasibleContainingZeroOutsideAnchorFlagIsometry_octad 1)
  refine ⟨w⁻¹, ?_, ?_⟩
  · exact generatedFeasibleContaining_inverse_transports _ _ _ hw
  · exact generatedFeasibleContaining_inverse_transports _ _ _ hp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
