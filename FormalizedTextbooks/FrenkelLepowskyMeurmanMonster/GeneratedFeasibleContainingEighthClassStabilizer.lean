/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingEighthInputRecognition

/-! Exact simultaneous orbit and stabilizer of the actual one-eighth destination.
These counts concern the simultaneous subgroup N; the whole A stabilizer is separate. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

/-- A one-eighth input lies in a single genuine simultaneous orbit of the entire incoming axis. -/
theorem generatedFeasibleContaining_eighth_input_incoming_orbit
    (h : localAxisStabilizer generatedFeasiblePhysicalRootPair)
    (hc : Quotient.mk (QuotientGroup.rightRel
      (localFeasibleTransitionSubgroup generatedFeasiblePhysicalRootPair)) h ∈
        generatedFeasibleContainingOutgoingCoefficientInputs 1) :
    rhoLocal h.val generatedFeasibleContainingOctadDestination ∈
      generatedFeasibleContainingCoordinateNOrbit generatedFeasibleContainingNewIncoming := by
  let a := generatedFeasibleContainingInverseSecondaryAddresses
    (Quotient.mk (QuotientGroup.rightRel
      (localFeasibleTransitionSubgroup generatedFeasiblePhysicalRootPair)) h)
  let k := generatedFeasibleContainingEighthAnchorWord
  let b := generatedFeasibleContainingInverseSecondaryAddresses
    (Quotient.mk (QuotientGroup.rightRel
      (localFeasibleTransitionSubgroup generatedFeasiblePhysicalRootPair)) k)
  have hS := (generatedFeasibleContainingOutgoingCoefficientInputs_word_iff h 1).mp hc
  have hP : griessShortIntegral a.val.1 0 = griessShortIntegral a.val.1 1 := by
    have hm := a.property
    change a.val ∈ generatedFeasibleOrthogonalShortLabels ×ˢ Finset.univ at hm
    rw [Finset.mem_product] at hm
    exact (generatedFeasibleOrthogonalShortLabels_mem a.val.1).mp hm.1
  obtain ⟨u, huS, huR⟩ := generatedFeasibleContaining_selected_eight_signed_transport
    a.val.1 a.val.2 b.val.2 hS hP
  have hb : b.val.1 = generatedFeasibleContainingNormalizedShortLabel :=
    generatedFeasibleContainingEighthAnchorWord_inverse_label
  have hm : rhoLocal u.val
      (rhoLocal h.val⁻¹ (generatedFeasibleSecondaryAxis generatedFeasiblePhysicalRootPair)) =
        rhoLocal k.val⁻¹ (generatedFeasibleSecondaryAxis generatedFeasiblePhysicalRootPair) := by
    rw [← generatedFeasibleContainingInverseSecondaryAddresses_axis h,
      ← generatedFeasibleContainingInverseSecondaryAddresses_axis k]
    change rhoLocal u.val (conwayShortAxis a.val.1 a.val.2) =
      conwayShortAxis b.val.1 b.val.2
    rw [hb]
    exact huR
  let n := k * u * h⁻¹
  have hn : n ∈ localFeasibleTransitionSubgroup generatedFeasiblePhysicalRootPair := by
    rw [← generatedFeasibleSecondaryAxis_stabilizer]
    change rhoLocal ((k.val * u.val) * h.val⁻¹) _ = _
    rw [map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hm, map_inv]
    exact (rhoLocal k.val).apply_symm_apply _
  let m : GeneratedFeasibleContainingN :=
    ⟨n⁻¹.val, n⁻¹.property, (localFeasibleTransitionSubgroup _).inv_mem hn⟩
  refine ⟨m, ?_⟩
  change rhoLocal ((k.val * u.val * h.val⁻¹)⁻¹)
    (rhoLocal k.val generatedFeasibleContainingOctadDestination) = _
  rw [mul_inv_rev, mul_inv_rev, inv_inv]
  rw [← mul_assoc]
  rw [map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply, map_inv, map_inv]
  change rhoLocal h.val ((rhoLocal u.val).symm
    ((rhoLocal k.val).symm (rhoLocal k.val generatedFeasibleContainingOctadDestination))) = _
  rw [LinearEquiv.symm_apply_apply]
  have hi : (rhoLocal u.val).symm generatedFeasibleContainingOctadDestination =
      generatedFeasibleContainingOctadDestination := by
    apply (rhoLocal u.val).injective
    rw [LinearEquiv.apply_symm_apply, huS]
  rw [hi]

/-- The original 64,512-input fibre is exactly the coset sector of the whole incoming N orbit. -/
theorem generatedFeasibleContaining_eighth_sector_cosets :
    generatedFeasibleContainingCoordinateSectorCosets generatedFeasibleContainingNewIncoming =
      generatedFeasibleContainingOutgoingCoefficientInputs 1 := by
  ext c
  induction c using Quotient.inductionOn with
  | h h =>
    constructor
    · rintro ⟨v, hv, n, hn⟩
      have hmate : (griessConwayEncode
          (rhoLocal v.val generatedFeasibleContainingOctadDestination)).2.1
            generatedFeasibleMateLabel = 0 := by
        rw [← hn, generatedFeasibleContaining_N_mate_coordinate,
          generatedFeasibleContainingNewIncoming_mate_zero]
      have hfirst : (griessConwayEncode
          (sExtra (rhoLocal v.val generatedFeasibleContainingOctadDestination))).2.1
            (Sum.inl (0, generatedFeasiblePhysicalRootPair)) = 1 / 8 := by
        obtain ⟨l, hl⟩ := generatedFeasibleContaining_N_triality_word n
        rw [← hn, ← hl]
        exact (generatedFeasibleContaining_first_coordinate_invariant _
          ⟨l.val, l.property.1⟩ _).trans
          generatedFeasibleContainingNewDestination_first_coordinate
      rw [← hv]
      refine ⟨(generatedFeasibleContaining_noncoordinate_input_word_iff v).mpr
        ⟨⟨v, rfl⟩, hmate⟩, ?_⟩
      exact hfirst
    · intro hc
      exact ⟨h, rfl, generatedFeasibleContaining_eighth_input_incoming_orbit h hc⟩

/-- Exactly 5,046,272 actual vectors form the incoming simultaneous orbit. -/
theorem generatedFeasibleContainingEighthIncoming_N_orbit_card :
    Nat.card (generatedFeasibleContainingCoordinateNOrbit
      generatedFeasibleContainingNewIncoming) = 5046272 := by
  have h := generatedFeasibleContainingCoordinateSector_balance
    generatedFeasibleContainingNewIncoming
    (generatedFeasibleContaining_NOrbit_subset_A _ _
      generatedFeasibleContainingNewIncoming_orbit)
  rw [generatedFeasibleContaining_eighth_sector_cosets,
    generatedFeasibleContainingOutgoingCoefficientInputs_card,
    Nat.card_congr (localFeasibleTransitionEquiv _).toEquiv,
    localOmegaAxisIntersection_card,
    generatedFeasibleContainingDestinationStabilizer_card] at h
  norm_num only [Matrix.cons_val_one, Matrix.cons_val_zero] at h
  omega

/-- Triality gives the exact same count for the actual one-eighth destination N orbit. -/
theorem generatedFeasibleContainingEighthDestination_N_orbit_card :
    Nat.card (generatedFeasibleContainingCoordinateNOrbit
      generatedFeasibleContainingNewDestination) = 5046272 := by
  change Nat.card (generatedFeasibleContainingCoordinateNOrbit
    (sExtra generatedFeasibleContainingNewIncoming)) = 5046272
  rw [generatedFeasibleContaining_N_triality_card]
  exact generatedFeasibleContainingEighthIncoming_N_orbit_card

/-- The actual simultaneous stabilizer of the entire independently defined destination. -/
def generatedFeasibleContainingEighthNStabilizer : Subgroup GeneratedFeasibleContainingN :=
  MulAction.stabilizer GeneratedFeasibleContainingN generatedFeasibleContainingNewDestination

/-- The genuine simultaneous action orbit equals the original range presentation. -/
theorem generatedFeasibleContainingEighthN_action_orbit :
    MulAction.orbit GeneratedFeasibleContainingN generatedFeasibleContainingNewDestination =
      generatedFeasibleContainingCoordinateNOrbit generatedFeasibleContainingNewDestination := by
  rfl

/-- The simultaneous stabilizer of the actual sixth destination has exactly 1,509,949,440 elements.
No cardinality of the whole A orbit is assumed. -/
theorem generatedFeasibleContainingEighthNStabilizer_card :
    Nat.card generatedFeasibleContainingEighthNStabilizer = 1509949440 := by
  have h := generatedFeasibleContainingEighthNStabilizer.card_mul_index
  rw [generatedFeasibleContainingEighthNStabilizer, MulAction.index_stabilizer,
    ← Nat.card_coe_set_eq, generatedFeasibleContainingEighthN_action_orbit,
    generatedFeasibleContainingEighthDestination_N_orbit_card,
    localOmegaAxisIntersection_card] at h
  apply Nat.eq_of_mul_eq_mul_right (by decide : 0 < 5046272)
  exact h.trans (by decide)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
