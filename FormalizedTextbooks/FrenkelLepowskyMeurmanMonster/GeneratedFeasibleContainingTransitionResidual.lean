/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingNoncoordinatePhasePartition

/-! Exact actual input cosets remaining after both containing coordinate returns. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

/-- Sector membership of a genuine coset is exactly sector membership of its actual word image.
-/
theorem generatedFeasibleContaining_sector_coset_word_iff (y : GriessSpace)
    (h : localAxisStabilizer generatedFeasiblePhysicalRootPair) :
    Quotient.mk (QuotientGroup.rightRel
        (localFeasibleTransitionSubgroup generatedFeasiblePhysicalRootPair)) h ∈
      generatedFeasibleContainingCoordinateSectorCosets y ↔
        rhoLocal h.val generatedFeasibleContainingOctadDestination ∈
          generatedFeasibleContainingCoordinateNOrbit y := by
  constructor
  · rintro ⟨u, hu, n, hn⟩
    have hm := QuotientGroup.rightRel_apply.mp (Quotient.exact' hu)
    change (h * u⁻¹).val ∈ localOmegaStabilizer at hm
    let k : GeneratedFeasibleContainingN :=
      ⟨(h * u⁻¹).val * n.val,
        (localAxisStabilizer generatedFeasiblePhysicalRootPair).mul_mem
          (h * u⁻¹).property n.property.1,
        localOmegaStabilizer.mul_mem hm n.property.2⟩
    refine ⟨k, ?_⟩
    change rhoLocal ((h.val * u.val⁻¹) * n.val) y =
      rhoLocal h.val generatedFeasibleContainingOctadDestination
    rw [map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    change rhoLocal n.val y = rhoLocal u.val generatedFeasibleContainingOctadDestination at hn
    rw [hn, map_inv]
    change rhoLocal h.val ((rhoLocal u.val).symm
      (rhoLocal u.val generatedFeasibleContainingOctadDestination)) = _
    rw [LinearEquiv.symm_apply_apply]
  · intro hh
    exact ⟨h, rfl, hh⟩

/-- All original input cosets in the two complete coordinate phase sectors. -/
def generatedFeasibleContainingCoordinateInputCosets :
    Set (generatedFeasibleTransitionCosetSpace generatedFeasiblePhysicalRootPair) :=
  generatedFeasibleContainingCoordinateSectorCosets generatedFeasibleContainingOctadDestination ∪
    generatedFeasibleContainingCoordinateSectorCosets generatedFeasibleContainingTrialitySquare

/-- Genuine input cosets whose actual containing vector lies in the noncoordinate remainder. -/
def generatedFeasibleContainingNoncoordinateInputCosets :
    Set (generatedFeasibleTransitionCosetSpace generatedFeasiblePhysicalRootPair) :=
  Set.univ \ generatedFeasibleContainingCoordinateInputCosets

/-- The two genuine coordinate input sectors have no common actual coset. -/
theorem generatedFeasibleContaining_coordinate_input_disjoint :
    Disjoint
      (generatedFeasibleContainingCoordinateSectorCosets
        generatedFeasibleContainingOctadDestination)
      (generatedFeasibleContainingCoordinateSectorCosets
        generatedFeasibleContainingTrialitySquare) := by
  apply Set.disjoint_left.mpr
  intro c
  induction c using Quotient.inductionOn with
  | h h =>
    intro hfirst hsecond
    rw [generatedFeasibleContaining_sector_coset_word_iff] at hfirst hsecond
    exact Set.disjoint_left.mp generatedFeasibleContainingCoordinateNOrbits_disjoint hfirst hsecond

/-- Exactly 126 original input cosets belong to the two proved coordinate phase sectors. -/
theorem generatedFeasibleContainingCoordinateInputCosets_card :
    Nat.card generatedFeasibleContainingCoordinateInputCosets = 126 := by
  have : Finite (generatedFeasibleContainingCoordinateSectorCosets
      generatedFeasibleContainingOctadDestination) := Nat.finite_of_card_ne_zero (by
    rw [generatedFeasibleContainingCoordinateFirst_cosets_card]
    decide)
  have : Finite (generatedFeasibleContainingCoordinateSectorCosets
      generatedFeasibleContainingTrialitySquare) := Nat.finite_of_card_ne_zero (by
    rw [generatedFeasibleContainingCoordinateSecond_cosets_card]
    decide)
  rw [generatedFeasibleContainingCoordinateInputCosets, Nat.card_coe_set_eq,
    Set.ncard_union_eq generatedFeasibleContaining_coordinate_input_disjoint,
    ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq,
    generatedFeasibleContainingCoordinateFirst_cosets_card,
    generatedFeasibleContainingCoordinateSecond_cosets_card]

/-- The genuine residual contains exactly 93,024 original input cosets. -/
theorem generatedFeasibleContainingNoncoordinateInputCosets_card :
    Nat.card generatedFeasibleContainingNoncoordinateInputCosets = 93024 := by
  have : Finite (generatedFeasibleTransitionCosetSpace generatedFeasiblePhysicalRootPair) :=
    Nat.finite_of_card_ne_zero (by
      rw [generatedFeasibleTransitionCosetSpace_card]
      decide)
  rw [generatedFeasibleContainingNoncoordinateInputCosets, Nat.card_coe_set_eq,
    Set.ncard_sdiff' (Set.subset_univ _), ← Nat.card_coe_set_eq, Nat.card_univ,
    generatedFeasibleTransitionCosetSpace_card, ← Nat.card_coe_set_eq,
    generatedFeasibleContainingCoordinateInputCosets_card]

/-- Every original coset representative lies in the residual exactly when its actual mate is zero.
-/
theorem generatedFeasibleContaining_noncoordinate_input_word_iff
    (h : localAxisStabilizer generatedFeasiblePhysicalRootPair) :
    Quotient.mk (QuotientGroup.rightRel
        (localFeasibleTransitionSubgroup generatedFeasiblePhysicalRootPair)) h ∈
      generatedFeasibleContainingNoncoordinateInputCosets ↔
        rhoLocal h.val generatedFeasibleContainingOctadDestination ∈
          generatedFeasibleContainingNoncoordinateAxes := by
  simp only [generatedFeasibleContainingNoncoordinateInputCosets, Set.mem_sdiff,
    Set.mem_univ, true_and, generatedFeasibleContainingCoordinateInputCosets]
  rw [Set.mem_union, not_or, generatedFeasibleContaining_sector_coset_word_iff,
    generatedFeasibleContaining_sector_coset_word_iff]
  have hx : rhoLocal h.val generatedFeasibleContainingOctadDestination ∈
      MulAction.orbit (localAxisStabilizer generatedFeasiblePhysicalRootPair)
        generatedFeasibleContainingOctadDestination := MulAction.mem_orbit _ h
  constructor
  · intro hn
    refine ⟨hx, (generatedFeasibleContaining_mate_zero_iff_noncoordinate _ hx).mpr ?_⟩
    exact not_or.mpr hn
  · rintro ⟨_, hm⟩
    exact not_or.mp ((generatedFeasibleContaining_mate_zero_iff_noncoordinate _ hx).mp hm)

/-- The actual residual is precisely the complement of the complete self and secondary returns.
No identification of any further A destination is assumed. -/
theorem generatedFeasibleContaining_transition_residual_eq :
    generatedFeasibleContainingNoncoordinateInputCosets = Set.univ \
      (generatedFeasibleActualTransitionCosets generatedFeasiblePhysicalRootPair
        generatedFeasibleContainingOctadDestination generatedFeasibleContainingOctadDestination ∪
      generatedFeasibleActualTransitionCosets generatedFeasiblePhysicalRootPair
        generatedFeasibleContainingOctadDestination
          (generatedFeasibleSecondaryAxis generatedFeasiblePhysicalRootPair)) := by
  rw [generatedFeasibleContaining_self_return_cosets_eq,
    ← generatedFeasibleContainingCoordinateSecond_cosets_eq]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
