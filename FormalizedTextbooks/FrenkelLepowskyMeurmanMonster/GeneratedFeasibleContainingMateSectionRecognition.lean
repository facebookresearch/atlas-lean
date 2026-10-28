/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingCoordinatePhaseCoverage

/-! A nonzero actual mate coefficient forces the rooted section into the coordinate catalogue. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
open Multiplicative
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

/-- The two genuine preferred pair roots add to an actual norm-eight coordinate frame. -/
theorem generatedFeasibleContaining_pair_frame (p : Fin 276) :
    griessShortLatticeVector (Sum.inl (0, p)) +
      griessShortLatticeVector (Sum.inl (1, p)) =
        leechCoordinateFrameLattice (griessCoordinatePair p).1 := by
  apply Subtype.ext
  funext i
  have hn := griessCoordinatePair_ne p
  simp only [griessShortLatticeVector, griessShortIntegral,
    leechCoordinateFrameLattice, leechCoordinateFrameVector, Submodule.coe_add, Pi.add_apply]
  by_cases ha : i = (griessCoordinatePair p).1 <;>
    by_cases hb : i = (griessCoordinatePair p).2 <;> simp_all

/-- Preferred mate classes differ from the original root class by the actual Omega frame class. -/
theorem generatedFeasibleContaining_pair_mate_class (p : Fin 276) :
    griessShortClass (Sum.inl (1, p)) =
      leechReduction (leechCoordinateFrameLattice 0) +
        griessShortClass (Sum.inl (0, p)) := by
  have hv : griessShortLatticeVector (Sum.inl (1, p)) =
      leechCoordinateFrameLattice (griessCoordinatePair p).1 -
        griessShortLatticeVector (Sum.inl (0, p)) := by
    rw [← generatedFeasibleContaining_pair_frame p]
    abel
  unfold griessShortClass
  rw [hv, map_sub, sub_eq_add_neg, ← map_neg, leechReduction_neg, leechFrame_reduction_eq]

/-- Actual monomial transport of a preferred minus root transports its preferred mate label too.
-/
theorem generatedFeasibleContaining_monomial_mate_label (g : leechIsomSubgroup)
    (hg : g ∈ golayMonomialSubgroup) (p q : Fin 276)
    (hp : griessShortPermutation g (Sum.inl (0, p)) = Sum.inl (0, q)) :
    griessShortPermutation g (Sum.inl (1, p)) = Sum.inl (1, q) := by
  apply griessShortClass_injective
  rw [griessShortPermutation_class, generatedFeasibleContaining_pair_mate_class, map_add]
  have hΩ : leechModTwoAction g (leechReduction (leechCoordinateFrameLattice 0)) =
      leechReduction (leechCoordinateFrameLattice 0) :=
    leechFrameClass_stabilizer_eq_monomial.ge hg
  rw [hΩ, ← griessShortPermutation_class, hp, generatedFeasibleContaining_pair_mate_class]

/-- Every genuine old containing-axis short coefficient is nonzero exactly on its actual section.
-/
theorem generatedFeasibleContaining_old_section_support
    (y : MulAction.orbit (localAxisStabilizer generatedFeasibleContainingIncidentPair)
      (generatedOctadLocalAxis 0 0)) (r : GriessShortIndex) :
    (griessConwayEncode y.val).2.1 r ≠ 0 ↔
      r ∈ generatedAxisE8ShortLines
        (generatedFeasibleContainingAxisRootedSectionMap y).val := by
  obtain ⟨a, ha⟩ := y.property
  change rhoLocal a.val (generatedOctadLocalAxis 0 0) = y.val at ha
  obtain ⟨f, hf⟩ := QuotientGroup.mk'_surjective localDiagonalSubgroup a.val
  change localFiberIntoH f = a.val at hf
  have hy : y = ⟨rhoLocal a.val (generatedOctadLocalAxis 0 0), ⟨a, rfl⟩⟩ :=
    Subtype.ext ha.symm
  rw [hy, generatedFeasibleContainingAxisRootedSectionMap_image a f hf]
  obtain ⟨s, hs⟩ := (griessShortPermutation f.val.2).surjective r
  rw [← hs]
  change (griessConwayEncode (rhoLocal a.val (generatedOctadLocalAxis 0 0))).2.1
      (griessShortPermutation f.val.2 s) ≠ 0 ↔
    griessShortPermutation f.val.2 s ∈ generatedAxisE8ShortLines
      ((generatedAxisE8CoordinateSection (golayOctadWord generatedOctadBasisOctad)).map
        (leechIntegralAction f.val.2).toLinearMap)
  rw [generatedAxisE8ShortLines_image_mem, generatedAxisE8ShortLines_coordinate_mem]
  rw [← hf]
  change (griessConwayEncode (localGriessRepresentation f
    (generatedOctadLocalAxis 0 0))).2.1 (griessShortPermutation f.val.2 s) ≠ 0 ↔ _
  rw [localGriessRepresentation_encode]
  change localShortOperator f
    (griessConwayEncode (generatedOctadLocalAxis 0 0)).2.1
      (griessShortPermutation f.val.2 s) ≠ 0 ↔ _
  rw [localShortOperator_image, mul_ne_zero_iff]
  have hn : qSign (localShortPhase f s) ≠ 0 := by
    have h := qSign_sq (localShortPhase f s)
    intro hz
    rw [hz] at h
    norm_num at h
  constructor
  · intro hs
    exact (generatedAxis_triality_octad_support_iff _ _ _ _).mp hs.2
  · intro hs
    exact ⟨hn, (generatedAxis_triality_octad_support_iff _ _ _ _).mpr hs⟩

/-- Nonzero actual source mate coefficients put the original incident mate in the rooted section.
-/
theorem generatedFeasibleContaining_source_mate_in_section
    (x : MulAction.orbit (localAxisStabilizer generatedFeasiblePhysicalRootPair)
      generatedFeasibleContainingOctadDestination)
    (hm : (griessConwayEncode x.val).2.1 generatedFeasibleMateLabel ≠ 0) :
    Sum.inl (1, generatedFeasibleContainingIncidentPair) ∈ generatedAxisE8ShortLines
      (generatedFeasibleContainingCoordinateSourceSectionMap x).val := by
  let h := generatedFeasibleContainingCoordinateSourceWord
  obtain ⟨t, ht⟩ := QuotientGroup.mk'_surjective localDiagonalSubgroup h.val
  change localFiberIntoH t = h.val at ht
  have htmon : t.val.2 ∈ golayMonomialSubgroup :=
    generatedFeasible_localOmega_lift_monomial t (ht.symm ▸ h.property)
  have hfirst := generatedFeasibleContainingCoordinateSourceWord_first
  change rhoLocal h.val (conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 0) =
    conwayShortAxis (Sum.inl (0, generatedFeasibleContainingIncidentPair)) 0 at hfirst
  rw [← ht] at hfirst
  change localGriessRepresentation t (conwayShortAxis
    (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 0) = _ at hfirst
  rw [generatedAxis_localFiber_image] at hfirst
  have hp : (griessShortPermutation t.val.2 (Sum.inl (0, generatedFeasiblePhysicalRootPair)),
      localShortPhase t (Sum.inl (0, generatedFeasiblePhysicalRootPair)) + 0) =
      (Sum.inl (0, generatedFeasibleContainingIncidentPair), 0) :=
    generatedAxis_signed_injective hfirst
  have hmate := generatedFeasibleContaining_monomial_mate_label t.val.2 htmon
    generatedFeasiblePhysicalRootPair generatedFeasibleContainingIncidentPair
    (congrArg Prod.fst hp)
  apply (generatedFeasibleContaining_old_section_support
    (generatedFeasibleContainingCoordinateSourceOrbitEquiv x) _).mp
  change (griessConwayEncode (rhoLocal h.val x.val)).2.1
    (Sum.inl (1, generatedFeasibleContainingIncidentPair)) ≠ 0
  rw [← hmate, ← ht]
  change (griessConwayEncode (localGriessRepresentation t x.val)).2.1
    (griessShortPermutation t.val.2 generatedFeasibleMateLabel) ≠ 0
  rw [localGriessRepresentation_encode]
  change localShortOperator t (griessConwayEncode x.val).2.1
    (griessShortPermutation t.val.2 generatedFeasibleMateLabel) ≠ 0
  rw [localShortOperator_image, mul_ne_zero_iff]
  refine ⟨?_, hm⟩
  intro hz
  have hs := qSign_sq (localShortPhase t generatedFeasibleMateLabel)
  rw [hz] at hs
  norm_num at hs

/-- The actual rooted section contains a genuine norm-eight frame when its mate is present. -/
theorem generatedFeasibleContaining_mate_section_frame
    (S : generatedFeasibleContainingRootedSections)
    (hm : Sum.inl (1, generatedFeasibleContainingIncidentPair) ∈ generatedAxisE8ShortLines S.val) :
    leechCoordinateFrameLattice 8 ∈ S.val ∧
      leechReduction (leechCoordinateFrameLattice 0) ∈ generatedAxisE8FrameClasses S.val := by
  have hframe := S.val.add_mem S.property.2 hm
  rw [generatedFeasibleContaining_pair_frame,
    generatedFeasibleContainingIncidentPair_coordinates] at hframe
  change leechCoordinateFrameLattice 8 ∈ S.val at hframe
  exact ⟨hframe, ⟨leechCoordinateFrameLattice 8, hframe,
    leechCoordinateFrameVector_square 8, leechFrame_reduction_eq 8⟩⟩

/-- Actual mate incidence recognizes one of the complete 77 original coordinate rooted sections.
-/
theorem generatedFeasibleContaining_mate_section_coordinate
    (S : generatedFeasibleContainingRootedSections)
    (hm : Sum.inl (1, generatedFeasibleContainingIncidentPair) ∈ generatedAxisE8ShortLines S.val) :
    S ∈ generatedFeasibleContainingCoordinateIncidentRootedSections := by
  obtain ⟨g, hg⟩ := S.property.1
  change generatedAxisE8ImageSection g (golayOctadWord generatedOctadBasisOctad) = S.val at hg
  have hb := (generatedFeasibleContaining_mate_section_frame S hm).2
  rw [← hg] at hb
  have hi := (generatedFeasibleContaining_coordinate_root_mem
    (golayOctadWord generatedOctadBasisOctad)).mp
      generatedFeasibleContainingRootedSections_initial.2
  obtain ⟨m, hmmon, hgm⟩ := generatedAxisE8_rooted_monomial
    (golayOctadWord generatedOctadBasisOctad) (golayOctadWord_mem_code _)
    (golayOctadWord_weight _) 8 hi.1 g hb
  obtain ⟨p, hp⟩ := generatedAxisE8_monomial_image
    (golayOctadWord generatedOctadBasisOctad) m hmmon
  have hS : S.val = generatedAxisE8CoordinateSection
      (golayPermute p (golayOctadWord generatedOctadBasisOctad)) :=
    hg.symm.trans (hgm.trans hp)
  change S.val ∈ generatedFeasibleContainingCoordinateIncidentSections
  rw [hS]
  apply generatedFeasibleContainingCoordinateIncidentSections_of_word
  · exact (p.property _).mp (golayOctadWord_mem_code _)
  · exact (Equiv.sum_comp p.val.symm
      (fun i => (golayOctadWord generatedOctadBasisOctad i).val)).trans
        (golayOctadWord_weight _)
  · rw [← hS]
    exact S.property.2

/-- A nonzero genuine source mate coefficient forces the complete actual coordinate phase sector.
-/
theorem generatedFeasibleContaining_mate_nonzero_coordinate
    (x : MulAction.orbit (localAxisStabilizer generatedFeasiblePhysicalRootPair)
      generatedFeasibleContainingOctadDestination)
    (hm : (griessConwayEncode x.val).2.1 generatedFeasibleMateLabel ≠ 0) :
    x.val ∈ generatedFeasibleContainingCoordinatePhaseSectors := by
  rw [generatedFeasibleContainingCoordinatePhaseSectors_eq_all_coordinate_phases]
  refine ⟨⟨x, ?_⟩, rfl⟩
  exact generatedFeasibleContaining_mate_section_coordinate _
    (generatedFeasibleContaining_source_mate_in_section x hm)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
