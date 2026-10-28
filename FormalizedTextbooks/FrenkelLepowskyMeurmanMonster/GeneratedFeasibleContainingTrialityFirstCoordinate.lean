/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingMatrixContraction
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFourthQShortBasisTriality

/-! Actual first-coordinate and unit-short bounds for the containing self-return exclusion. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

/-- The entire genuine first-axis stabilizer preserves its original preferred short coefficient.
-/
theorem generatedFeasibleContaining_first_coordinate_invariant (p : Fin 276)
    (a : localAxisStabilizer p) (x : GriessSpace) :
    (griessConwayEncode (rhoLocal a.val x)).2.1 (Sum.inl (0, p)) =
      (griessConwayEncode x).2.1 (Sum.inl (0, p)) := by
  obtain ⟨f, hf⟩ := QuotientGroup.mk'_surjective localDiagonalSubgroup a.val
  change localFiberIntoH f = a.val at hf
  have hp := (localAxisStabilizer_mk_iff f p).mp (hf.symm ▸ a.property)
  rw [← hf]
  change (griessConwayEncode (localGriessRepresentation f x)).2.1 _ = _
  rw [localGriessRepresentation_encode, localConwayRawRepresentation_apply]
  have hi := localShortOperator_image f (griessConwayEncode x).2.1 (Sum.inl (0, p))
  rw [hp.1, hp.2, qSign_zero, one_mul] at hi
  exact hi

/-- The original containing source has first-root preferred coefficient exactly one. -/
theorem generatedFeasibleContaining_source_first_coordinate :
    (griessConwayEncode generatedFeasibleContainingOctadDestination).2.1
      (Sum.inl (0, generatedFeasiblePhysicalRootPair)) = 1 := by
  unfold generatedFeasibleContainingOctadDestination generatedFeasibleContainingOctadPrototypeLabel
  rw [generatedAxis_triality_octad_pair_coordinate, generatedFeasiblePhysicalRootPair_coordinates]
  norm_num only [Fin.reduceEq, ite_true, one_mul]
  exact generatedFeasibleContaining_prototype_pair_product

/-- Every actual containing A-vector has the original first coefficient exactly one. -/
theorem generatedFeasibleContaining_first_coordinate (x : GriessSpace)
    (hx : x ∈ MulAction.orbit (localAxisStabilizer generatedFeasiblePhysicalRootPair)
      generatedFeasibleContainingOctadDestination) :
    (griessConwayEncode x).2.1 (Sum.inl (0, generatedFeasiblePhysicalRootPair)) = 1 := by
  obtain ⟨a, ha⟩ := MulAction.mem_orbit_iff.mp hx
  change rhoLocal a.val generatedFeasibleContainingOctadDestination = x at ha
  rw [← ha, generatedFeasibleContaining_first_coordinate_invariant]
  exact generatedFeasibleContaining_source_first_coordinate

/-- The complete original 120-coordinate support has only unit short coefficients or zero. -/
theorem generatedFeasibleContaining_source_short_unit (r : GriessShortIndex) :
    (griessConwayEncode generatedFeasibleContainingOctadDestination).2.1 r *
        (griessConwayEncode generatedFeasibleContainingOctadDestination).2.1 r = 1 ∨
      (griessConwayEncode generatedFeasibleContainingOctadDestination).2.1 r = 0 := by
  by_cases hs : generatedOctadShortSupport generatedFeasibleContainingOctadPrototypeIndex r
  · left
    change (griessConwayEncode (sExtra (conwayShortAxis
      (Sum.inr (Sum.inl (generatedFeasibleContainingOctadPrototypeIndex, 0))) 0))).2.1 r *
      (griessConwayEncode (sExtra (conwayShortAxis
        (Sum.inr (Sum.inl (generatedFeasibleContainingOctadPrototypeIndex, 0))) 0))).2.1 r = 1
    rw [← pow_two]
    exact generatedAxis_triality_octad_supported_square _ _ _ _ hs
  · right
    exact generatedAxis_triality_octad_unsupported_zero _ _ _ _ hs

/-- Genuine signed spatial transport preserves the complete unit-or-zero short bound. -/
theorem generatedFeasibleContaining_short_unit (x : GriessSpace)
    (hx : x ∈ MulAction.orbit (localAxisStabilizer generatedFeasiblePhysicalRootPair)
      generatedFeasibleContainingOctadDestination) (r : GriessShortIndex) :
    (griessConwayEncode x).2.1 r * (griessConwayEncode x).2.1 r = 1 ∨
      (griessConwayEncode x).2.1 r = 0 := by
  obtain ⟨a, ha⟩ := MulAction.mem_orbit_iff.mp hx
  change rhoLocal a.val generatedFeasibleContainingOctadDestination = x at ha
  obtain ⟨f, hf⟩ := QuotientGroup.mk'_surjective localDiagonalSubgroup a.val
  change localFiberIntoH f = a.val at hf
  obtain ⟨s, hs⟩ := (griessShortPermutation f.val.2).surjective r
  rw [← ha, ← hf, ← hs]
  change (griessConwayEncode (localGriessRepresentation f
      generatedFeasibleContainingOctadDestination)).2.1 (griessShortPermutation f.val.2 s) *
      (griessConwayEncode (localGriessRepresentation f
        generatedFeasibleContainingOctadDestination)).2.1 (griessShortPermutation f.val.2 s) = 1 ∨
      (griessConwayEncode (localGriessRepresentation f
        generatedFeasibleContainingOctadDestination)).2.1 (griessShortPermutation f.val.2 s) = 0
  rw [localGriessRepresentation_encode, localConwayRawRepresentation_apply]
  change localShortOperator f (griessConwayEncode
      generatedFeasibleContainingOctadDestination).2.1 (griessShortPermutation f.val.2 s) *
      localShortOperator f (griessConwayEncode
        generatedFeasibleContainingOctadDestination).2.1 (griessShortPermutation f.val.2 s) = 1 ∨
      localShortOperator f (griessConwayEncode
        generatedFeasibleContainingOctadDestination).2.1 (griessShortPermutation f.val.2 s) = 0
  rw [localShortOperator_image]
  rcases generatedFeasibleContaining_source_short_unit s with hu | hz
  · left
    calc
      _ = (qSign (localShortPhase f s) * qSign (localShortPhase f s)) *
          ((griessConwayEncode generatedFeasibleContainingOctadDestination).2.1 s *
            (griessConwayEncode generatedFeasibleContainingOctadDestination).2.1 s) := by ring
      _ = 1 := by rw [qSign_sq, hu, one_mul]
  · right
    rw [hz, mul_zero]

/-- The exact genuine dictionary formula at the fixed original first-root coordinates. -/
theorem generatedFeasibleContaining_triality_first_coordinate (x : GriessSpace) :
    (griessConwayEncode (sExtra x)).2.1 (Sum.inl (0, generatedFeasiblePhysicalRootPair)) =
      (griessConwayEncode x).1 0 1 +
        ((griessConwayEncode x).2.1 (Sum.inl (0, generatedFeasiblePhysicalRootPair)) -
          (griessConwayEncode x).2.1 generatedFeasibleMateLabel) / 2 := by
  rw [generatedFourthQShortBasis_triality_pair_minus,
    generatedFeasiblePhysicalRootPair_coordinates]
  rfl

/-- A genuine containing self-return has mate coefficient exactly minus one. -/
theorem generatedFeasibleContaining_self_return_mate (x : GriessSpace)
    (hx : x ∈ MulAction.orbit (localAxisStabilizer generatedFeasiblePhysicalRootPair)
      generatedFeasibleContainingOctadDestination)
    (ht : sExtra x ∈ MulAction.orbit (localAxisStabilizer generatedFeasiblePhysicalRootPair)
      generatedFeasibleContainingOctadDestination) :
    (griessConwayEncode x).2.1 generatedFeasibleMateLabel = -1 := by
  have hf := generatedFeasibleContaining_first_coordinate x hx
  have hft := generatedFeasibleContaining_first_coordinate (sExtra x) ht
  rw [generatedFeasibleContaining_triality_first_coordinate, hf] at hft
  have hp := generatedFeasibleContaining_matrix_first_offdiag_nonpos x hx
  rcases generatedFeasibleContaining_short_unit x hx generatedFeasibleMateLabel with hu | hz
  · nlinarith
  · rw [hz] at hft
    linarith

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
