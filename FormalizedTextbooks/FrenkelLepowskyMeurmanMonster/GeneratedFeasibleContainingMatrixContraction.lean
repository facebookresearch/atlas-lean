/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingCoordinatePhaseCoverage

/-! Actual containing-axis projections are contractions at the fixed original root coordinates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

/-- Entry formula for the genuine spatial action on an arbitrary coordinate projection. -/
theorem generatedFeasibleContaining_projection_entry (g : leechIsomSubgroup)
    (w : Fin 24 → ℝ) (i j : Fin 24) :
    conwayMatrixAction g (Matrix.diagonal w) i j =
      ∑ k : Fin 24, w k * leechIsomMatrix g i k * leechIsomMatrix g j k := by
  rw [conwayMatrixAction_eq_conjugate]
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- All original coordinate projections stay symmetric under actual lattice isometries. -/
theorem generatedFeasibleContaining_projection_symmetric (g : leechIsomSubgroup)
    (w : Fin 24 → ℝ) (i j : Fin 24) :
    conwayMatrixAction g (Matrix.diagonal w) i j =
      conwayMatrixAction g (Matrix.diagonal w) j i := by
  rw [generatedFeasibleContaining_projection_entry, generatedFeasibleContaining_projection_entry]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Every diagonal entry of the actual image of a zero-one coordinate projection is at most one.
-/
theorem generatedFeasibleContaining_projection_diagonal_le_one (g : leechIsomSubgroup)
    (b : Fin 24 → Bool) (i : Fin 24) :
    conwayMatrixAction g (Matrix.diagonal (fun k => if b k then (1 : ℝ) else 0)) i i ≤ 1 := by
  rw [generatedFeasibleContaining_projection_entry]
  have hn : (∑ k : Fin 24, leechIsomMatrix g i k * leechIsomMatrix g i k) = 1 := by
    have h := congrArg (fun M : Matrix (Fin 24) (Fin 24) ℝ => M i i)
      (mul_eq_one_comm.mp (leechIsomMatrix_transpose_mul g))
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply_eq] using h
  calc
    _ ≤ ∑ k : Fin 24, leechIsomMatrix g i k * leechIsomMatrix g i k := by
      apply Finset.sum_le_sum
      intro k _
      cases b k
      · simp only [Bool.false_eq_true, ite_false, zero_mul]
        exact mul_self_nonneg _
      · simp
    _ = 1 := hn

/-- Every genuine containing A-orbit matrix is an actual image of the original coordinate projector.
-/
theorem generatedFeasibleContaining_matrix_image (x : GriessSpace)
    (hx : x ∈ MulAction.orbit (localAxisStabilizer generatedFeasiblePhysicalRootPair)
      generatedFeasibleContainingOctadDestination) :
    ∃ g : leechIsomSubgroup, (griessConwayEncode x).1 =
      conwayMatrixAction g (Matrix.diagonal (fun i : Fin 24 =>
        if (golayEncodedMask 2063).testBit i.val then (1 : ℝ) else 0)) := by
  obtain ⟨a, ha⟩ := MulAction.mem_orbit_iff.mp hx
  change rhoLocal a.val generatedFeasibleContainingOctadDestination = x at ha
  obtain ⟨f, hf⟩ := QuotientGroup.mk'_surjective localDiagonalSubgroup a.val
  change localFiberIntoH f = a.val at hf
  refine ⟨f.val.2, ?_⟩
  rw [← ha, ← hf]
  change (griessConwayEncode (localGriessRepresentation f
    generatedFeasibleContainingOctadDestination)).1 = _
  rw [localGriessRepresentation_encode, localConwayRawRepresentation_apply,
    generatedFeasibleContainingOctadDestination, generatedFeasibleContainingOctadPrototypeLabel,
    generatedAxis_triality_octad_matrix, generatedFeasibleContainingOctadPrototypeIndex_label]
  rfl

/-- Actual containing A-orbit matrices are symmetric at every original coordinate. -/
theorem generatedFeasibleContaining_matrix_symmetric (x : GriessSpace)
    (hx : x ∈ MulAction.orbit (localAxisStabilizer generatedFeasiblePhysicalRootPair)
      generatedFeasibleContainingOctadDestination) (i j : Fin 24) :
    (griessConwayEncode x).1 i j = (griessConwayEncode x).1 j i := by
  obtain ⟨g, hg⟩ := generatedFeasibleContaining_matrix_image x hx
  rw [hg]
  exact generatedFeasibleContaining_projection_symmetric _ _ _ _

/-- Every genuine containing A-orbit diagonal entry is at most one. -/
theorem generatedFeasibleContaining_matrix_diagonal_le_one (x : GriessSpace)
    (hx : x ∈ MulAction.orbit (localAxisStabilizer generatedFeasiblePhysicalRootPair)
      generatedFeasibleContainingOctadDestination) (i : Fin 24) :
    (griessConwayEncode x).1 i i ≤ 1 := by
  obtain ⟨g, hg⟩ := generatedFeasibleContaining_matrix_image x hx
  rw [hg]
  exact generatedFeasibleContaining_projection_diagonal_le_one _ _ _

/-- The genuine preferred minus-pair evaluates an arbitrary original matrix explicitly. -/
theorem generatedFeasibleContaining_minus_pairing (P : Matrix (Fin 24) (Fin 24) ℝ)
    (p : Fin 276) :
    conwayShortPairing P (Sum.inl (0, p)) =
      2 * (P (griessCoordinatePair p).1 (griessCoordinatePair p).1 +
        P (griessCoordinatePair p).2 (griessCoordinatePair p).2 -
        P (griessCoordinatePair p).1 (griessCoordinatePair p).2 -
        P (griessCoordinatePair p).2 (griessCoordinatePair p).1) := by
  have ho (i j : Fin 24) :
      griessShortVector (Sum.inl (0, p)) i * griessShortVector (Sum.inl (0, p)) j =
        2 * (trialityPairProjection p i j - trialityPairMatrix p i j) := by
    linarith [griessPair_outer_coordinate_sum p i j,
      griessPair_outer_coordinate_difference p i j]
  unfold conwayShortPairing
  simp_rw [mul_assoc, ho]
  simp only [trialityPairProjection, Matrix.diagonal_apply, trialityPairMatrix_apply]
  simp only [mul_sub, mul_add, mul_ite, mul_zero, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]
  ring

/-- Every actual containing A-vector has the original anchored matrix pairing four. -/
theorem generatedFeasibleContaining_matrix_pairing_four (x : GriessSpace)
    (hx : x ∈ MulAction.orbit (localAxisStabilizer generatedFeasiblePhysicalRootPair)
      generatedFeasibleContainingOctadDestination) :
    conwayShortPairing (griessConwayEncode x).1
      (Sum.inl (0, generatedFeasiblePhysicalRootPair)) = 4 := by
  obtain ⟨a, ha⟩ := MulAction.mem_orbit_iff.mp hx
  change rhoLocal a.val generatedFeasibleContainingOctadDestination = x at ha
  rw [← ha]
  exact (generatedFeasibleAnchoredMatrixPairing_invariant _ _ _).trans
    generatedFeasibleContainingOctadDestination_anchored_pairing

/-- Contraction and the actual fixed-root pairing force the source off-diagonal to be nonpositive.
-/
theorem generatedFeasibleContaining_matrix_first_offdiag_nonpos (x : GriessSpace)
    (hx : x ∈ MulAction.orbit (localAxisStabilizer generatedFeasiblePhysicalRootPair)
      generatedFeasibleContainingOctadDestination) :
    (griessConwayEncode x).1 0 1 ≤ 0 := by
  have hp := generatedFeasibleContaining_matrix_pairing_four x hx
  rw [generatedFeasibleContaining_minus_pairing,
    generatedFeasiblePhysicalRootPair_coordinates] at hp
  have hs := generatedFeasibleContaining_matrix_symmetric x hx 1 0
  have h0 := generatedFeasibleContaining_matrix_diagonal_le_one x hx 0
  have h1 := generatedFeasibleContaining_matrix_diagonal_le_one x hx 1
  dsimp only [Prod.fst, Prod.snd] at hp
  linarith

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
