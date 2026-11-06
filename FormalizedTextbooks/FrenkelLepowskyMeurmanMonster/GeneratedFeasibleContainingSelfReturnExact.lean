/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingMateSectionRecognition
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingTrialityFirstCoordinate

/-! Complete actual containing self-return recognition and exact original 63-coset fiber. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

/-- Across the complete actual containing A orbit, mate minus one recognizes the first N sector.
-/
theorem generatedFeasibleContaining_mate_minus_one_iff_first_sector (x : GriessSpace)
    (hx : x ∈ MulAction.orbit (localAxisStabilizer generatedFeasiblePhysicalRootPair)
      generatedFeasibleContainingOctadDestination) :
    (griessConwayEncode x).2.1 generatedFeasibleMateLabel = -1 ↔
      x ∈ generatedFeasibleContainingCoordinateNOrbit
        generatedFeasibleContainingOctadDestination := by
  constructor
  · intro hm
    have hn : (griessConwayEncode x).2.1 generatedFeasibleMateLabel ≠ 0 := by
      rw [hm]
      norm_num
    have hs := generatedFeasibleContaining_mate_nonzero_coordinate ⟨x, hx⟩ hn
    change x ∈ generatedFeasibleContainingCoordinateNOrbit
        generatedFeasibleContainingOctadDestination ∪
      generatedFeasibleContainingCoordinateNOrbit generatedFeasibleContainingTrialitySquare at hs
    rcases hs with hs | ⟨n, hnx⟩
    · exact hs
    · rw [← hnx, generatedFeasibleContaining_N_mate_coordinate,
        generatedFeasibleContainingCoordinateSecond_mate] at hm
      norm_num at hm
  · rintro ⟨n, rfl⟩
    rw [generatedFeasibleContaining_N_mate_coordinate,
      generatedFeasibleContainingCoordinateFirst_mate]

/-- The complete actual containing self-return vector fiber is precisely the first N sector.
-/
theorem generatedFeasibleContaining_self_return_vectors_eq :
    generatedFeasibleTransitionVectors generatedFeasiblePhysicalRootPair
      generatedFeasibleContainingOctadDestination generatedFeasibleContainingOctadDestination =
        generatedFeasibleContainingCoordinateNOrbit
          generatedFeasibleContainingOctadDestination := by
  apply Set.Subset.antisymm
  · rintro x ⟨hx, ht⟩
    exact (generatedFeasibleContaining_mate_minus_one_iff_first_sector x hx).mp
      (generatedFeasibleContaining_self_return_mate x hx ht)
  · exact generatedFeasibleContainingCoordinateFirst_self_return

/-- Every original containing self-return vector is covered; the genuine fiber has 4928 vectors.
-/
theorem generatedFeasibleContaining_self_return_vectors_card :
    Nat.card (generatedFeasibleTransitionVectors generatedFeasiblePhysicalRootPair
      generatedFeasibleContainingOctadDestination generatedFeasibleContainingOctadDestination) =
        4928 := by
  rw [generatedFeasibleContaining_self_return_vectors_eq]
  exact generatedFeasibleContainingCoordinateFirstNOrbit_card

/-- Mate minus one is the exact actual self-return condition on the whole containing A orbit.
-/
theorem generatedFeasibleContaining_self_return_iff_mate (x : GriessSpace)
    (hx : x ∈ MulAction.orbit (localAxisStabilizer generatedFeasiblePhysicalRootPair)
      generatedFeasibleContainingOctadDestination) :
    sExtra x ∈ MulAction.orbit (localAxisStabilizer generatedFeasiblePhysicalRootPair)
      generatedFeasibleContainingOctadDestination ↔
        (griessConwayEncode x).2.1 generatedFeasibleMateLabel = -1 := by
  constructor
  · exact generatedFeasibleContaining_self_return_mate x hx
  · intro hm
    have hs := (generatedFeasibleContaining_mate_minus_one_iff_first_sector x hx).mp hm
    exact (generatedFeasibleContainingCoordinateFirst_self_return hs).2

/-- The complete original containing self-return cosets coincide with the proved first sector.
-/
theorem generatedFeasibleContaining_self_return_cosets_eq :
    generatedFeasibleActualTransitionCosets generatedFeasiblePhysicalRootPair
      generatedFeasibleContainingOctadDestination generatedFeasibleContainingOctadDestination =
        generatedFeasibleContainingCoordinateSectorCosets
          generatedFeasibleContainingOctadDestination := by
  apply Set.Subset.antisymm
  · intro c
    induction c using Quotient.inductionOn with
    | h h =>
      intro hc
      refine ⟨h, rfl, ?_⟩
      rw [← generatedFeasibleContaining_self_return_vectors_eq]
      refine ⟨MulAction.mem_orbit _ h, ?_⟩
      change Quotient.mk (MulAction.orbitRel
        (localAxisStabilizer generatedFeasiblePhysicalRootPair) GriessSpace)
          (sExtra (rhoLocal h.val generatedFeasibleContainingOctadDestination)) =
            Quotient.mk (MulAction.orbitRel
              (localAxisStabilizer generatedFeasiblePhysicalRootPair) GriessSpace)
                generatedFeasibleContainingOctadDestination at hc
      exact MulAction.orbitRel_apply.mp (Quotient.exact' hc)
  · exact generatedFeasibleContainingCoordinateSectorCosets_subset _ _
      generatedFeasibleContainingCoordinateFirst_self_return

/-- The full actual containing self-transition column contains exactly 63 original cosets. -/
theorem generatedFeasibleContaining_self_return_cosets_card :
    Nat.card (generatedFeasibleActualTransitionCosets generatedFeasiblePhysicalRootPair
      generatedFeasibleContainingOctadDestination generatedFeasibleContainingOctadDestination) =
        63 := by
  rw [generatedFeasibleContaining_self_return_cosets_eq]
  exact generatedFeasibleContainingCoordinateFirst_cosets_card

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
