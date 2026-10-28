/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleSecondaryActualTransitionCounts
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisOctadOrbitCount
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8ShortFlagStabilizer

/-! Genuine transport of the containing destination and fixed root to the old octad source. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The genuine incident minus-pair root on coordinates eight and nine. -/
def generatedFeasibleContainingIncidentPair : Fin 276 := griessPairIndex 8 9 (by decide)

/-- The incident root address is bound to its actual physical coordinates. -/
theorem generatedFeasibleContainingIncidentPair_coordinates :
    griessCoordinatePair generatedFeasibleContainingIncidentPair = (8, 9) := by
  rw [generatedFeasibleContainingIncidentPair, griessPairIndex_coordinates]
  rfl

/-- The old globally counted octad axis is the actual outside prototype used above. -/
theorem generatedFeasibleContaining_old_octad_axis :
    generatedOctadLocalAxis 0 0 = generatedFeasibleOutsideOctadDestination := rfl

private theorem source_word :
    ∃ p : golayAutomorphismSubgroup, p.val 0 = 8 ∧ p.val 1 = 9 ∧
      golayPermute p.val golayStandardOctad = golayEncoder (golayLabelCoefficients 3) := by
  let a : Fin 5 → Fin 24 := fun j => ⟨8 + j.val, by omega⟩
  let b : Fin 5 → Fin 24 := fun j => Fin.castAdd 19 j
  have ha : Function.Injective a := by
    intro i j h
    have hh := congrArg (fun k : Fin 24 => k.val) h
    apply Fin.ext
    dsimp [a] at hh
    omega
  have hb : Function.Injective b := by
    intro i j h
    exact Fin.ext (congrArg (fun k : Fin 24 => k.val) h)
  obtain ⟨q, hq⟩ := golayAutomorphism_five_transitive a b ha hb
  have hw : (∑ i : Fin 24, (golayEncoder (golayLabelCoefficients 3) i).val) = 8 := by
    decide +kernel
  have hs : ∀ j : Fin 5, golayEncoder (golayLabelCoefficients 3) (a j) = 1 := by
    decide +kernel
  have he : golayPermute q.val (golayEncoder (golayLabelCoefficients 3)) =
      golayStandardOctad := by
    apply golayOctad_unique_through_first_five _ _
      ((q.property _).mp ⟨_, rfl⟩) golayStandardOctad_mem
      ((Equiv.sum_comp q.val.symm
        (fun i => (golayEncoder (golayLabelCoefficients 3) i).val)).trans hw)
      golayStandardOctad_weight
    intro i hi
    let j : Fin 5 := ⟨i.val, hi⟩
    have hbi : b j = i := Fin.ext rfl
    have hqi : q.val.symm i = a j := by rw [← hbi, ← hq j, q.val.symm_apply_apply]
    refine ⟨?_, ?_⟩
    · change golayEncoder (golayLabelCoefficients 3) (q.val.symm i) = 1
      rw [hqi]
      exact hs j
    · simp [golayStandardOctad, show i.val < 8 by omega]
  refine ⟨q⁻¹, ?_, ?_, ?_⟩
  · change q.val.symm 0 = 8
    apply q.val.symm_apply_eq.mpr
    exact (hq 0).symm
  · change q.val.symm 1 = 9
    apply q.val.symm_apply_eq.mpr
    exact (hq 1).symm
  · funext i
    have hi := congrFun he (q.val i)
    change golayEncoder (golayLabelCoefficients 3) (q.val.symm (q.val i)) =
      golayStandardOctad (q.val i) at hi
    rw [q.val.symm_apply_apply] at hi
    exact hi.symm

/-- A genuine source Mathieu word transports both original preferred root and octad lines. -/
theorem generatedFeasibleContaining_source_monomial :
    ∃ e : leechIsomSubgroup, e ∈ golayMonomialSubgroup ∧
      griessShortPermutation e (Sum.inl (0, generatedFeasiblePhysicalRootPair)) =
        Sum.inl (0, generatedFeasibleContainingIncidentPair) ∧
      griessShortPermutation e generatedFeasibleContainingOctadPrototypeLabel =
        generatedFeasibleOutsideOctadPrototypeLabel := by
  obtain ⟨p, hp0, hp1, hp⟩ := source_word
  let e := golayPermutationIsometry p
  have hz : golaySignIsometry 0 = 1 := golaySignHom.map_one
  have he : e ∈ golayMonomialSubgroup :=
    ⟨0, p, by simp [e, hz]⟩
  refine ⟨e, he, ?_, ?_⟩
  · apply (leechRootedA2_short_perm_eq_iff _ _ _).mpr
    left
    apply Subtype.ext
    rw [leechIntegralAction_golayPermutation]
    funext i
    have h0 : p.val.symm i = 0 ↔ i = 8 := by rw [Equiv.symm_apply_eq, hp0]
    have h1 : p.val.symm i = 1 ↔ i = 9 := by rw [Equiv.symm_apply_eq, hp1]
    simp only [golayIntegerPermute, griessShortLatticeVector, griessShortIntegral,
      generatedFeasiblePhysicalRootPair_coordinates,
      generatedFeasibleContainingIncidentPair_coordinates, h0, h1, ite_true]
  · apply (leechRootedA2_short_perm_eq_iff _ _ _).mpr
    left
    apply Subtype.ext
    rw [leechIntegralAction_golayPermutation]
    funext i
    change griessShortIntegral generatedFeasibleContainingOctadPrototypeLabel
      (p.val.symm i) = griessShortIntegral generatedFeasibleOutsideOctadPrototypeLabel i
    rw [generatedFeasibleContainingOctadPrototype_integral,
      generatedFeasibleOutsideOctadPrototype_integral]
    have hi := congrFun hp i
    have hcode : ∀ j : Fin 24, golayEncoder (golayLabelCoefficients 3) j =
        if 8 ≤ j.val ∧ j.val < 16 then 1 else 0 := by decide +kernel
    change golayStandardOctad (p.val.symm i) = golayEncoder (golayLabelCoefficients 3) i at hi
    rw [hcode] at hi
    unfold golayStandardOctad at hi
    split_ifs at hi ⊢ <;> simp_all

private theorem incident_mate_base :
    toAdd (griessShortQ (Sum.inl (1, generatedFeasibleContainingIncidentPair))).base =
      toAdd sourceOmegaQ.base +
        toAdd (griessShortQ (Sum.inl (0, generatedFeasibleContainingIncidentPair))).base := by
  have hv : griessShortLatticeVector (Sum.inl (1, generatedFeasibleContainingIncidentPair)) =
      leechCoordinateFrameLattice 8 -
        griessShortLatticeVector (Sum.inl (0, generatedFeasibleContainingIncidentPair)) := by
    apply Subtype.ext
    funext i
    simp only [griessShortLatticeVector, griessShortIntegral,
      generatedFeasibleContainingIncidentPair_coordinates, leechCoordinateFrameLattice,
      leechCoordinateFrameVector, Submodule.coe_sub, Pi.sub_apply]
    by_cases h8 : i = 8 <;> by_cases h9 : i = 9 <;> simp_all
  have hs : griessShortClass (Sum.inl (1, generatedFeasibleContainingIncidentPair)) =
      leechReduction (leechCoordinateFrameLattice 0) +
        griessShortClass (Sum.inl (0, generatedFeasibleContainingIncidentPair)) := by
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
    (griessShortQ generatedFeasibleOutsideOctadPrototypeLabel).base ≠
        (griessShortQ (Sum.inl (0, generatedFeasibleContainingIncidentPair))).base ∧
      toAdd (griessShortQ generatedFeasibleOutsideOctadPrototypeLabel).base ≠
        toAdd sourceOmegaQ.base +
          toAdd (griessShortQ (Sum.inl (0, generatedFeasibleContainingIncidentPair))).base := by
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
        conwayShortAxis (Sum.inl (0, generatedFeasibleContainingIncidentPair)) 0 ∧
      rhoLocal h.val (conwayShortAxis generatedFeasibleContainingOctadPrototypeLabel 0) =
        conwayShortAxis generatedFeasibleOutsideOctadPrototypeLabel 0 := by
  obtain ⟨e, he, hfirst, hoctad⟩ := generatedFeasibleContaining_source_monomial
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
    (Sum.inl (0, generatedFeasibleContainingIncidentPair))
    (localShortPhase f (Sum.inl (0, generatedFeasiblePhysicalRootPair)))
  let f' := localFiberIncl q * f
  have hzero : localShortPhase f' (Sum.inl (0, generatedFeasiblePhysicalRootPair)) = 0 := by
    rw [localShortPhase_mul, hlf, hphase]
    exact CharTwo.add_self_eq_zero _
  have hfp : griessShortPermutation f'.val.2 (Sum.inl (0, generatedFeasiblePhysicalRootPair)) =
      Sum.inl (0, generatedFeasibleContainingIncidentPair) := by
    change griessShortPermutation (1 * f.val.2) _ = _
    simpa only [one_mul] using hlf
  have hfo : griessShortPermutation f'.val.2 generatedFeasibleContainingOctadPrototypeLabel =
      generatedFeasibleOutsideOctadPrototypeLabel := by
    change griessShortPermutation (1 * f.val.2) _ = _
    simpa only [one_mul] using (hl _).trans hoctad
  have hΩ : localFiberIntoH f' ∈ localOmegaStabilizer := by
    change inclQ q * localFiberIntoH f ∈ localOmegaStabilizer
    rw [hf]
    exact localOmegaStabilizer.mul_mem hqΩ h.property
  have hr : rhoLocal (localFiberIntoH f')
      (conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 0) =
        conwayShortAxis (Sum.inl (0, generatedFeasibleContainingIncidentPair)) 0 := by
    change localGriessRepresentation f' _ = _
    rw [generatedAxis_localFiber_image, hfp, hzero, add_zero]
  have ho : rhoLocal (localFiberIntoH f')
      (conwayShortAxis generatedFeasibleContainingOctadPrototypeLabel 0) =
        conwayShortAxis generatedFeasibleOutsideOctadPrototypeLabel
          (localShortPhase f' generatedFeasibleContainingOctadPrototypeLabel) := by
    change localGriessRepresentation f' _ = _
    rw [generatedAxis_localFiber_image, hfo, add_zero]
  obtain ⟨k, hk⟩ := generatedFeasible_independent_short_signed
    generatedFeasibleContainingIncidentPair generatedFeasibleOutsideOctadPrototypeLabel
    incident_octad_independent.1 incident_octad_independent.2
    (localShortPhase f' generatedFeasibleContainingOctadPrototypeLabel) 0
  refine ⟨⟨k.val * localFiberIntoH f',
    localOmegaStabilizer.mul_mem k.property.2 hΩ⟩, ?_, ?_⟩
  · rw [rhoLocal.map_mul, LinearEquiv.mul_apply, hr]
    exact localAxisStabilizer_signedAxis_fixed k.val _ k.property.1 0
  · rw [rhoLocal.map_mul, LinearEquiv.mul_apply, ho]
    exact hk

/-- One genuine local word transports both the fixed positive root and containing destination
to the incident root and the original globally counted octad axis. -/
theorem generatedFeasibleContaining_source_transport :
    ∃ h : H,
      rhoLocal h (conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 0) =
        conwayShortAxis (Sum.inl (0, generatedFeasibleContainingIncidentPair)) 0 ∧
      rhoLocal h generatedFeasibleContainingOctadDestination = generatedOctadLocalAxis 0 0 := by
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
      (sExtra (conwayShortAxis generatedFeasibleContainingOctadPrototypeLabel 0)) =
      sExtra (conwayShortAxis generatedFeasibleOutsideOctadPrototypeLabel 0)
    rw [hh, hnoctad]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
