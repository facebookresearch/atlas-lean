/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingCoordinateTransitionReturns

/-! The actual source-to-old containing transport retains its original Omega stabilizer. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

private theorem coordinate_incident_mate_base :
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

private theorem coordinate_incident_octad_independent :
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
    rw [← coordinate_incident_mate_base] at he
    have hi := generatedFeasible_short_base_injective (toAdd.injective he)
    cases hi

private theorem coordinate_source_signed_transport :
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
    coordinate_incident_octad_independent.1 coordinate_incident_octad_independent.2
    (localShortPhase f' generatedFeasibleContainingOctadPrototypeLabel) 0
  refine ⟨⟨k.val * localFiberIntoH f',
    localOmegaStabilizer.mul_mem k.property.2 hΩ⟩, ?_, ?_⟩
  · rw [rhoLocal.map_mul, LinearEquiv.mul_apply, hr]
    exact localAxisStabilizer_signedAxis_fixed k.val _ k.property.1 0
  · rw [rhoLocal.map_mul, LinearEquiv.mul_apply, ho]
    exact hk

/-- One genuine local word transports both the fixed positive root and containing destination
to the incident root and the original globally counted octad axis. -/
theorem generatedFeasibleContaining_coordinate_source_transport :
    ∃ h : localOmegaStabilizer,
      rhoLocal h.val (conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 0) =
        conwayShortAxis (Sum.inl (0, generatedFeasibleContainingIncidentPair)) 0 ∧
      rhoLocal h.val generatedFeasibleContainingOctadDestination = generatedOctadLocalAxis 0 0 := by
  obtain ⟨n, hnfirst, hnoctad⟩ := coordinate_source_signed_transport
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
  refine ⟨h, ?_, ?_⟩
  · have he := hh (conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 0)
    rw [hnfirst, generatedAxis_triality_pair_exact, generatedAxis_triality_pair_exact] at he
    exact he
  · change rhoLocal h.val
      (sExtra (conwayShortAxis generatedFeasibleContainingOctadPrototypeLabel 0)) =
      sExtra (conwayShortAxis generatedFeasibleOutsideOctadPrototypeLabel 0)
    rw [hh, hnoctad]


/-- A selected genuine Omega word transports both complete original containing vectors. -/
def generatedFeasibleContainingCoordinateSourceWord : localOmegaStabilizer :=
  Classical.choose generatedFeasibleContaining_coordinate_source_transport

/-- The selected word transports the entire original fixed root. -/
theorem generatedFeasibleContainingCoordinateSourceWord_first :
    rhoLocal generatedFeasibleContainingCoordinateSourceWord.val
      (conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 0) =
        conwayShortAxis (Sum.inl (0, generatedFeasibleContainingIncidentPair)) 0 :=
  (Classical.choose_spec generatedFeasibleContaining_coordinate_source_transport).1

/-- The selected word transports the entire original containing destination. -/
theorem generatedFeasibleContainingCoordinateSourceWord_axis :
    rhoLocal generatedFeasibleContainingCoordinateSourceWord.val
      generatedFeasibleContainingOctadDestination = generatedOctadLocalAxis 0 0 :=
  (Classical.choose_spec generatedFeasibleContaining_coordinate_source_transport).2

/-- The actual whole-vector orbit equivalence induced by this original Omega word. -/
def generatedFeasibleContainingCoordinateSourceOrbitEquiv :=
  generatedFeasibleContainingSourceOrbitEquiv generatedFeasibleContainingCoordinateSourceWord.val
    generatedFeasibleContainingCoordinateSourceWord_first
    generatedFeasibleContainingCoordinateSourceWord_axis

/-- The selected source map keeps the already proved actual old rooted-section map. -/
def generatedFeasibleContainingCoordinateSourceSectionMap :
    MulAction.orbit (localAxisStabilizer generatedFeasiblePhysicalRootPair)
      generatedFeasibleContainingOctadDestination → generatedFeasibleContainingRootedSections :=
  fun x => generatedFeasibleContainingAxisRootedSectionMap
    (generatedFeasibleContainingCoordinateSourceOrbitEquiv x)

/-- Every actual rooted section has exactly128 genuine whole-axis vectors above this source map. -/
theorem generatedFeasibleContainingCoordinateSourceSectionMap_fiber_card
    (S : generatedFeasibleContainingRootedSections) :
    Nat.card (generatedFeasibleContainingCoordinateSourceSectionMap ⁻¹' {S}) = 128 := by
  change Nat.card ((fun x => (Equiv.refl generatedFeasibleContainingRootedSections)
    (generatedFeasibleContainingAxisRootedSectionMap
      (generatedFeasibleContainingCoordinateSourceOrbitEquiv x))) ⁻¹' {S}) = 128
  rw [Nat.card_congr (generatedFeasibleContainingMapFiberEquiv
    generatedFeasibleContainingCoordinateSourceOrbitEquiv
    (Equiv.refl generatedFeasibleContainingRootedSections)
    generatedFeasibleContainingAxisRootedSectionMap S)]
  exact generatedFeasibleContainingAxisRootedSectionMap_fiber_card S

/-- The selected genuine source map covers all original 56925 rooted sections. -/
theorem generatedFeasibleContainingCoordinateSourceSectionMap_surjective :
    Function.Surjective generatedFeasibleContainingCoordinateSourceSectionMap := by
  intro S
  obtain ⟨x, hx⟩ := generatedFeasibleContainingAxisRootedSectionMap_surjective S
  exact ⟨generatedFeasibleContainingCoordinateSourceOrbitEquiv.symm x, by
    change generatedFeasibleContainingAxisRootedSectionMap
      (generatedFeasibleContainingCoordinateSourceOrbitEquiv
        (generatedFeasibleContainingCoordinateSourceOrbitEquiv.symm x)) = S
    rw [Equiv.apply_symm_apply, hx]⟩

/-- Any genuine source word with monomial spatial lift maps to an actual old coordinate section. -/
theorem generatedFeasibleContainingCoordinateSourceSectionMap_monomial
    (a : localAxisStabilizer generatedFeasiblePhysicalRootPair)
    (f : localFiberSubgroup) (hf : localFiberIntoH f = a.val)
    (hm : f.val.2 ∈ golayMonomialSubgroup) :
    ∃ p : golayAutomorphismSubgroup,
      (generatedFeasibleContainingCoordinateSourceSectionMap
        ⟨rhoLocal a.val generatedFeasibleContainingOctadDestination, ⟨a, rfl⟩⟩).val =
          generatedAxisE8CoordinateSection
            (golayPermute p.val (golayOctadWord generatedOctadBasisOctad)) := by
  let h := generatedFeasibleContainingCoordinateSourceWord
  obtain ⟨t, ht⟩ := QuotientGroup.mk'_surjective localDiagonalSubgroup h.val
  change localFiberIntoH t = h.val at ht
  have htmon : t.val.2 ∈ golayMonomialSubgroup :=
    generatedFeasible_localOmega_lift_monomial t (ht.symm ▸ h.property)
  let k : localAxisStabilizer generatedFeasibleContainingIncidentPair :=
    ⟨h.val * a.val * h.val⁻¹, by
      change rhoLocal (h.val * a.val * h.val⁻¹)
        (conwayAxis generatedFeasibleContainingIncidentPair) =
          conwayAxis generatedFeasibleContainingIncidentPair
      have ha : rhoLocal a.val
          (conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 0) =
            conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 0 := by
        rw [conwayShortAxis_pair_zero]
        exact a.property
      simpa only [conwayShortAxis_pair_zero] using
        generatedFeasibleContaining_conjugate_fixes h.val a.val _ _
          generatedFeasibleContainingCoordinateSourceWord_first ha⟩
  let u : localFiberSubgroup := t * f * t⁻¹
  have hu : localFiberIntoH u = k.val := by
    change localFiberIntoH (t * f * t⁻¹) = h.val * a.val * h.val⁻¹
    rw [map_mul, map_mul, map_inv, ht, hf]
  have humon : u.val.2 ∈ golayMonomialSubgroup :=
    golayMonomialSubgroup.mul_mem (golayMonomialSubgroup.mul_mem htmon hm)
      (golayMonomialSubgroup.inv_mem htmon)
  have he : generatedFeasibleContainingCoordinateSourceOrbitEquiv
      ⟨rhoLocal a.val generatedFeasibleContainingOctadDestination, ⟨a, rfl⟩⟩ =
        ⟨rhoLocal k.val (generatedOctadLocalAxis 0 0), ⟨k, rfl⟩⟩ := by
    apply Subtype.ext
    change rhoLocal h.val (rhoLocal a.val generatedFeasibleContainingOctadDestination) =
      rhoLocal (h.val * a.val * h.val⁻¹) (generatedOctadLocalAxis 0 0)
    have hi := generatedFeasibleContaining_inverse_transports h.val _ _
      generatedFeasibleContainingCoordinateSourceWord_axis
    rw [map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hi]
  unfold generatedFeasibleContainingCoordinateSourceSectionMap
  rw [he, generatedFeasibleContainingAxisRootedSectionMap_image k u hu]
  exact generatedAxisE8_monomial_image _ u.val.2 humon

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
