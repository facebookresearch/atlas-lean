/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleSecondaryMateOrbit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOctadCoordinates

/-! An actual first-root matrix invariant separates two secondary triality destinations. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Evaluation of the original physical matrix on the fixed first short-root line. -/
def generatedFeasibleAnchoredMatrixPairing (p : Fin 276) (x : GriessSpace) : ℝ :=
  conwayShortPairing (griessConwayEncode x).1 (Sum.inl (0, p))

/-- The entire actual first-axis stabilizer preserves this original matrix evaluation. -/
theorem generatedFeasibleAnchoredMatrixPairing_invariant (p : Fin 276)
    (h : localAxisStabilizer p) (x : GriessSpace) :
    generatedFeasibleAnchoredMatrixPairing p (rhoLocal h.val x) =
      generatedFeasibleAnchoredMatrixPairing p x := by
  obtain ⟨f, hf⟩ := QuotientGroup.mk'_surjective localDiagonalSubgroup h.val
  have hfix := h.property
  rw [← hf] at hfix
  change localGriessRepresentation f (conwayAxis p) = conwayAxis p at hfix
  have hp := (localAxis_fiber_fixed_iff f p).mp hfix
  unfold generatedFeasibleAnchoredMatrixPairing
  rw [← hf]
  change conwayShortPairing (griessConwayEncode (localGriessRepresentation f x)).1 _ = _
  have hm := congrArg Prod.fst (localGriessRepresentation_encode f x)
  change (griessConwayEncode (localGriessRepresentation f x)).1 =
    conwayMatrixAction f.val.2 (griessConwayEncode x).1 at hm
  rw [hm]
  simpa only [hp.1] using
    conwayShortPairing_covariant f.val.2 (griessConwayEncode x).1 (Sum.inl (0, p))

/-- The containing-pair destination's projection contains the entire first root. -/
theorem generatedFeasibleContainingOctadDestination_anchored_pairing :
    generatedFeasibleAnchoredMatrixPairing generatedFeasiblePhysicalRootPair
      generatedFeasibleContainingOctadDestination = 4 := by
  unfold generatedFeasibleAnchoredMatrixPairing generatedFeasibleContainingOctadDestination
  unfold generatedFeasibleContainingOctadPrototypeLabel
  rw [generatedAxis_triality_octad_matrix, conwayShortPairing_diagonal_pair,
    generatedFeasiblePhysicalRootPair_coordinates,
    generatedFeasibleContainingOctadPrototypeIndex_label]
  have hs : (golayEncodedMask 2063).testBit 0 = true ∧
      (golayEncodedMask 2063).testBit 1 = true := by decide +kernel
  norm_num [hs.1, hs.2]

/-- The outside-pair destination's projection annihilates the entire first root. -/
theorem generatedFeasibleOutsideOctadDestination_anchored_pairing :
    generatedFeasibleAnchoredMatrixPairing generatedFeasiblePhysicalRootPair
      generatedFeasibleOutsideOctadDestination = 0 := by
  unfold generatedFeasibleAnchoredMatrixPairing generatedFeasibleOutsideOctadDestination
  unfold generatedFeasibleOutsideOctadPrototypeLabel
  rw [generatedAxis_triality_octad_matrix, conwayShortPairing_diagonal_pair,
    generatedFeasiblePhysicalRootPair_coordinates,
    generatedFeasibleOutsideOctadPrototypeIndex_label]
  have hs : (golayEncodedMask 3).testBit 0 = false ∧
      (golayEncodedMask 3).testBit 1 = false := by decide +kernel
  norm_num [hs.1, hs.2]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
