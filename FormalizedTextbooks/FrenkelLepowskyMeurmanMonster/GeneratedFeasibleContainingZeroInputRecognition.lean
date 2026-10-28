/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingZeroRootOrbitReachability

/-! Complete actual destination recognition for all original coefficient-zero inputs.
Identification of this actual orbit with the established outside class is a separate theorem. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

/-- The original external-pair anchor is perpendicular to the actual positive first root. -/
theorem generatedFeasibleContaining_zero_anchor_perpendicular :
    griessShortIntegral generatedFeasibleContainingZeroShortLabel 0 =
      griessShortIntegral generatedFeasibleContainingZeroShortLabel 1 := by
  have h0 := generatedFeasibleContainingZeroCachedIntegral_source_zero (Sum.inl (0, 0)) 0
  have h1 := generatedFeasibleContainingZeroCachedIntegral_source_zero (Sum.inl (0, 0)) 1
  rw [generatedFeasibleContainingZeroCachedIntegral_actual] at h0 h1
  exact h0.trans h1.symm

/-- The original preferred signed secondary address of the faithful zero-coefficient anchor. -/
def generatedFeasibleContainingZeroAnchorAddress : generatedFeasibleOrthogonalSignedShortLabels :=
  ⟨(generatedFeasibleContainingZeroShortLabel, 0), Finset.mem_product.mpr
    ⟨(generatedFeasibleOrthogonalShortLabels_mem _).mpr generatedFeasibleContaining_zero_anchor_perpendicular,
      Finset.mem_univ _⟩⟩

/-- The unique original inverse-secondary coset with this complete specified signed address. -/
def generatedFeasibleContainingZeroAnchorCoset :
    generatedFeasibleTransitionCosetSpace generatedFeasiblePhysicalRootPair :=
  generatedFeasibleContainingInverseSecondaryAddresses.symm
    generatedFeasibleContainingZeroAnchorAddress

/-- A representative in the actual original first-axis group of this fully constrained coset. -/
def generatedFeasibleContainingZeroAnchorWord :
    localAxisStabilizer generatedFeasiblePhysicalRootPair :=
  Classical.choose (Quotient.mk_surjective generatedFeasibleContainingZeroAnchorCoset)

/-- The actual word represents exactly the independently specified original inverse coset. -/
theorem generatedFeasibleContainingZeroAnchorWord_coset :
    Quotient.mk (QuotientGroup.rightRel
      (localFeasibleTransitionSubgroup generatedFeasiblePhysicalRootPair))
        generatedFeasibleContainingZeroAnchorWord =
      generatedFeasibleContainingZeroAnchorCoset :=
  Classical.choose_spec (Quotient.mk_surjective generatedFeasibleContainingZeroAnchorCoset)

/-- The entire actual inverse-secondary address, retaining the specified binary phase. -/
theorem generatedFeasibleContainingZeroAnchorWord_inverse_address :
    generatedFeasibleContainingInverseSecondaryAddresses
      (Quotient.mk (QuotientGroup.rightRel
        (localFeasibleTransitionSubgroup generatedFeasiblePhysicalRootPair))
          generatedFeasibleContainingZeroAnchorWord) =
        generatedFeasibleContainingZeroAnchorAddress := by
  rw [generatedFeasibleContainingZeroAnchorWord_coset]
  exact generatedFeasibleContainingInverseSecondaryAddresses.apply_symm_apply _

/-- The actual zero-coefficient destination axis defined through the faithful original action. -/
def generatedFeasibleContainingZeroDestination : GriessSpace :=
  sExtra (rhoLocal generatedFeasibleContainingZeroAnchorWord.val
    generatedFeasibleContainingOctadDestination)

/-- The original anchor word has precisely this actual destination class. -/
theorem generatedFeasibleContainingZeroAnchorWord_destination :
    generatedFeasibleTransitionDestination generatedFeasiblePhysicalRootPair
      generatedFeasibleContainingOctadDestination
        (Quotient.mk (QuotientGroup.rightRel
          (localFeasibleTransitionSubgroup generatedFeasiblePhysicalRootPair))
            generatedFeasibleContainingZeroAnchorWord) =
      generatedFeasibleSecondaryAClass generatedFeasibleContainingZeroDestination := rfl

/-- Every original selected-zero inverse coset address has the same faithful actual
zero-coefficient destination. The proof uses a genuine full signed source-stabilizer mover. -/
theorem generatedFeasibleContaining_zero_word_recognition
    (h : localAxisStabilizer generatedFeasiblePhysicalRootPair)
    (hS : generatedFeasibleContainingSelectedShortSquare
      (generatedFeasibleContainingInverseSecondaryAddresses
        (Quotient.mk (QuotientGroup.rightRel
          (localFeasibleTransitionSubgroup generatedFeasiblePhysicalRootPair)) h)).val.1 = 0) :
    generatedFeasibleTransitionDestination generatedFeasiblePhysicalRootPair
      generatedFeasibleContainingOctadDestination
        (Quotient.mk (QuotientGroup.rightRel
          (localFeasibleTransitionSubgroup generatedFeasiblePhysicalRootPair)) h) =
      generatedFeasibleSecondaryAClass generatedFeasibleContainingZeroDestination := by
  let a := generatedFeasibleContainingInverseSecondaryAddresses
    (Quotient.mk (QuotientGroup.rightRel
      (localFeasibleTransitionSubgroup generatedFeasiblePhysicalRootPair)) h)
  let k := generatedFeasibleContainingZeroAnchorWord
  let b := generatedFeasibleContainingInverseSecondaryAddresses
    (Quotient.mk (QuotientGroup.rightRel
      (localFeasibleTransitionSubgroup generatedFeasiblePhysicalRootPair)) k)
  obtain ⟨u, huS, huR⟩ := generatedFeasibleContaining_selected_zero_signed_transport
    a.val.1 a.val.2 b.val.2 hS
  have hb : b.val.1 = generatedFeasibleContainingZeroShortLabel :=
    congrArg (fun x : generatedFeasibleOrthogonalSignedShortLabels => x.val.1)
      generatedFeasibleContainingZeroAnchorWord_inverse_address
  have hm : rhoLocal u.val
      (rhoLocal h.val⁻¹ (generatedFeasibleSecondaryAxis generatedFeasiblePhysicalRootPair)) =
        rhoLocal k.val⁻¹ (generatedFeasibleSecondaryAxis generatedFeasiblePhysicalRootPair) := by
    rw [← generatedFeasibleContainingInverseSecondaryAddresses_axis h,
      ← generatedFeasibleContainingInverseSecondaryAddresses_axis k]
    change rhoLocal u.val (conwayShortAxis a.val.1 a.val.2) =
      conwayShortAxis b.val.1 b.val.2
    rw [hb]
    exact huR
  exact (generatedFeasibleContaining_destination_inverse_mover h k u huS hm).trans
    generatedFeasibleContainingZeroAnchorWord_destination

/-- Every one of the4,320 genuine zero-coefficient inputs from the complete original containing
transition has the faithful actual zero-coefficient destination. No class count is assumed. -/
theorem generatedFeasibleContaining_zero_input_recognition
    (c : generatedFeasibleTransitionCosetSpace generatedFeasiblePhysicalRootPair)
    (hc : c ∈ generatedFeasibleContainingOutgoingCoefficientInputs 0) :
    generatedFeasibleTransitionDestination generatedFeasiblePhysicalRootPair
      generatedFeasibleContainingOctadDestination c =
      generatedFeasibleSecondaryAClass generatedFeasibleContainingZeroDestination := by
  induction c using Quotient.inductionOn with
  | h h =>
      rw [generatedFeasibleContainingOutgoingCoefficientInputs_word_iff] at hc
      change generatedFeasibleContainingSelectedShortSquare
        (generatedFeasibleContainingInverseSecondaryAddresses
          (Quotient.mk (QuotientGroup.rightRel
            (localFeasibleTransitionSubgroup generatedFeasiblePhysicalRootPair)) h)).val.1 = 0 at hc
      exact generatedFeasibleContaining_zero_word_recognition h hc

/-- The actual destination has original first coefficient zero. This follows from the
proved nonempty original input fiber and actual recognition, without a class-size premise. -/
theorem generatedFeasibleContainingZeroDestination_first_coordinate :
    (griessConwayEncode generatedFeasibleContainingZeroDestination).2.1
      (Sum.inl (0, generatedFeasiblePhysicalRootPair)) = (0 : ℝ) := by
  have hn : Nat.card (generatedFeasibleContainingOutgoingCoefficientInputs 0) ≠ 0 := by
    rw [generatedFeasibleContainingOutgoingCoefficientInputs_card]
    decide
  obtain ⟨c⟩ := (Nat.card_ne_zero.mp hn).1
  have he := generatedFeasibleContaining_zero_input_recognition c.val c.property
  have hh := c.property.2
  change generatedFeasibleContainingAClassFirst
    (generatedFeasibleTransitionDestination generatedFeasiblePhysicalRootPair
      generatedFeasibleContainingOctadDestination c.val) = (0 : ℝ) at hh
  rw [he] at hh
  exact hh

/-- The entire original noncoordinate fiber of this faithful actual destination is exactly the
whole zero-coefficient input fiber, with all original signed addresses retained. -/
theorem generatedFeasibleContaining_zero_noncoordinate_input_iff
    (c : generatedFeasibleTransitionCosetSpace generatedFeasiblePhysicalRootPair)
    (hc : c ∈ generatedFeasibleContainingNoncoordinateInputCosets) :
    generatedFeasibleTransitionDestination generatedFeasiblePhysicalRootPair
      generatedFeasibleContainingOctadDestination c =
        generatedFeasibleSecondaryAClass generatedFeasibleContainingZeroDestination ↔
      c ∈ generatedFeasibleContainingOutgoingCoefficientInputs 0 := by
  constructor
  · intro he
    change c ∈ generatedFeasibleContainingNoncoordinateInputCosets ∧
      generatedFeasibleContainingInputFirst c = (0 : ℝ)
    refine ⟨hc, ?_⟩
    change generatedFeasibleContainingAClassFirst
      (generatedFeasibleTransitionDestination generatedFeasiblePhysicalRootPair
        generatedFeasibleContainingOctadDestination c) = _
    rw [he]
    exact generatedFeasibleContainingZeroDestination_first_coordinate
  · exact generatedFeasibleContaining_zero_input_recognition c

/-- Exactly4,320 original noncoordinate transition cosets reach this actual destination class.
This is an input count, and does not assert the global feasible class size or its stabilizer. -/
theorem generatedFeasibleContaining_zero_noncoordinate_class_input_card :
    Nat.card {c : generatedFeasibleTransitionCosetSpace generatedFeasiblePhysicalRootPair |
      c ∈ generatedFeasibleContainingNoncoordinateInputCosets ∧
      generatedFeasibleTransitionDestination generatedFeasiblePhysicalRootPair
        generatedFeasibleContainingOctadDestination c =
          generatedFeasibleSecondaryAClass generatedFeasibleContainingZeroDestination} =
      4320 := by
  have he : {c : generatedFeasibleTransitionCosetSpace generatedFeasiblePhysicalRootPair |
      c ∈ generatedFeasibleContainingNoncoordinateInputCosets ∧
      generatedFeasibleTransitionDestination generatedFeasiblePhysicalRootPair
        generatedFeasibleContainingOctadDestination c =
          generatedFeasibleSecondaryAClass generatedFeasibleContainingZeroDestination} =
      generatedFeasibleContainingOutgoingCoefficientInputs 0 := by
    ext c
    constructor
    · rintro ⟨hc, hd⟩
      exact (generatedFeasibleContaining_zero_noncoordinate_input_iff c hc).mp hd
    · intro hc
      exact ⟨hc.1, generatedFeasibleContaining_zero_input_recognition c hc⟩
  rw [he, generatedFeasibleContainingOutgoingCoefficientInputs_card]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
