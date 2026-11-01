/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingZeroOutsideAnchorTrialityPacket
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingZeroOutsideAnchorSourcePacket
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingZeroOutsideAnchorQImages

/-! The explicit whole actual outside-to-containing bridge retains its positive first root. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

/-- Actual original source octad2818, outside the first root1−2. -/
def generatedFeasibleContainingZeroOutsideAnchorSource : GriessSpace :=
  sExtra (conwayShortAxis (Sum.inr (Sum.inl
    (generatedFeasibleContainingZeroOutsideAnchorOctad 10, 0))) 0)

/-- Actual original target octad780, containing the positive first root1−2. -/
def generatedFeasibleContainingZeroOutsideAnchorTarget : GriessSpace :=
  sExtra (conwayShortAxis (Sum.inr (Sum.inl
    (generatedFeasibleContainingZeroOutsideAnchorOctad 6, 0))) 0)

/-- The first preferred root is bound to physical coordinates1 and2. -/
theorem generatedFeasibleContainingZeroOutsideAnchorFirst_coordinates :
    griessCoordinatePair (23 : Fin 276) = (1, 2) := by
  rw [← generatedAxisGlobalPairCoordinates_actual]
  decide +kernel

private theorem xi_matrix : leechIsomMatrix co1XiIsometry = co1XiMatrix := by
  ext i j
  change ∑ k, co1XiMatrix i k * (Pi.single j (1 : ℝ) : Fin 24 → ℝ) k = co1XiMatrix i j
  simp [Pi.single_apply]

private theorem xi_matrix_action (A : Matrix (Fin 24) (Fin 24) ℚ) :
    conwayMatrixAction co1XiIsometry (A.map (Rat.castHom ℝ)) =
      (co1XiMatrixQ * A * co1XiMatrixQ.transpose).map (Rat.castHom ℝ) := by
  rw [conwayMatrixAction_eq_conjugate, xi_matrix]
  simp only [co1XiMatrix, Matrix.map_mul, Matrix.transpose_map]

private theorem source_matrix :
    (griessConwayEncode generatedFeasibleContainingZeroOutsideAnchorSource).1 =
      generatedFeasibleContainingZeroOutsideAnchorSourceProjectionQ.map (Rat.castHom ℝ) := by
  rw [generatedFeasibleContainingZeroOutsideAnchorSource, generatedAxis_triality_octad_matrix]
  ext i j
  simp [generatedFeasibleContainingZeroOutsideAnchorSourceProjectionQ,
    generatedFeasibleContainingZeroOutsideAnchorOctad_label, Matrix.diagonal, Matrix.map_apply]
  split_ifs <;> simp

private theorem target_matrix :
    (griessConwayEncode generatedFeasibleContainingZeroOutsideAnchorTarget).1 =
      generatedFeasibleContainingZeroOutsideAnchorTargetProjectionQ.map (Rat.castHom ℝ) := by
  rw [generatedFeasibleContainingZeroOutsideAnchorTarget, generatedAxis_triality_octad_matrix]
  ext i j
  simp [generatedFeasibleContainingZeroOutsideAnchorTargetProjectionQ,
    generatedFeasibleContainingZeroOutsideAnchorOctad_label, Matrix.diagonal, Matrix.map_apply]
  split_ifs <;> simp

private theorem source_short :
    (griessConwayEncode generatedFeasibleContainingZeroOutsideAnchorSource).2.1 =
      ∑ n : Fin 120, (generatedFeasibleContainingZeroOutsideAnchorCoefficient 0 n : ℝ) •
        Pi.single (generatedFeasibleContainingZeroOutsideAnchorIndex (generatedFeasibleContainingZeroOutsideAnchorRoot 0 n)) (1 : ℝ) :=
  generatedFeasibleContainingZeroOutsideAnchorEnd_short 0

private theorem target_short :
    (griessConwayEncode generatedFeasibleContainingZeroOutsideAnchorTarget).2.1 =
      ∑ n : Fin 120, (generatedFeasibleContainingZeroOutsideAnchorCoefficient 3 n : ℝ) •
        Pi.single (generatedFeasibleContainingZeroOutsideAnchorIndex (generatedFeasibleContainingZeroOutsideAnchorRoot 3 n)) (1 : ℝ) :=
  generatedFeasibleContainingZeroOutsideAnchorEnd_short 1

private theorem step_zero_short :
    localShortOperator (generatedFeasibleContainingZeroOutsideAnchorStep 0)
      (∑ n : Fin 120, (generatedFeasibleContainingZeroOutsideAnchorCoefficient 0 n : ℝ) •
        Pi.single (generatedFeasibleContainingZeroOutsideAnchorIndex (generatedFeasibleContainingZeroOutsideAnchorRoot 0 n)) (1 : ℝ)) =
      ∑ n : Fin 120, (generatedFeasibleContainingZeroOutsideAnchorCoefficient 1 n : ℝ) •
        Pi.single (generatedFeasibleContainingZeroOutsideAnchorIndex (generatedFeasibleContainingZeroOutsideAnchorRoot 1 n)) (1 : ℝ) :=
  generatedFeasibleContainingZeroOutsideAnchorStep_short 0

private theorem step_one_short :
    localShortOperator (generatedFeasibleContainingZeroOutsideAnchorStep 1)
      (∑ n : Fin 120, (generatedFeasibleContainingZeroOutsideAnchorCoefficient 2 n : ℝ) •
        Pi.single (generatedFeasibleContainingZeroOutsideAnchorIndex (generatedFeasibleContainingZeroOutsideAnchorRoot 2 n)) (1 : ℝ)) =
      ∑ n : Fin 120, (generatedFeasibleContainingZeroOutsideAnchorCoefficient 3 n : ℝ) •
        Pi.single (generatedFeasibleContainingZeroOutsideAnchorIndex (generatedFeasibleContainingZeroOutsideAnchorRoot 3 n)) (1 : ℝ) :=
  generatedFeasibleContainingZeroOutsideAnchorStep_short 1

private theorem zero_tensor :
    (fun (_ : SpinIndex) (_ : Fin 24) => ((0 : ℚ) : ℝ) / Real.sqrt 2) = 0 := by
  funext t j
  simp

/-- The entire actual first corrected-Xi source is the full original rational packet. -/
theorem generatedFeasibleContainingZeroOutsideAnchorFirst_actual :
    griessConwayEncode (rhoLocal
      (localFiberIntoH (generatedFeasibleContainingZeroOutsideAnchorStep 0))
        generatedFeasibleContainingZeroOutsideAnchorSource) =
      generatedAxisGlobalRationalPacketReal generatedFeasibleContainingZeroOutsideAnchorFirstPacket := by
  change griessConwayEncode (localGriessRepresentation
    (generatedFeasibleContainingZeroOutsideAnchorStep 0)
      generatedFeasibleContainingZeroOutsideAnchorSource) = _
  rw [localGriessRepresentation_encode, localConwayRawRepresentation_apply]
  apply Prod.ext
  · change conwayMatrixAction (1 * co1XiIsometry)
      (griessConwayEncode generatedFeasibleContainingZeroOutsideAnchorSource).1 =
        generatedFeasibleContainingZeroOutsideAnchorMatrix1Q.map (Rat.castHom ℝ)
    rw [one_mul, source_matrix, xi_matrix_action,
      generatedFeasibleContainingZeroOutsideAnchorMatrix_source]
  · apply Prod.ext
    · change localShortOperator (generatedFeasibleContainingZeroOutsideAnchorStep 0)
        (griessConwayEncode generatedFeasibleContainingZeroOutsideAnchorSource).2.1 =
          fun r => (generatedFeasibleContainingZeroOutsideAnchorShortQ 1 r : ℝ)
      rw [source_short, step_zero_short, ← generatedFeasibleContainingZeroOutsideAnchorShortQ_sum 1]
    · change localTensorRepresentation (generatedFeasibleContainingZeroOutsideAnchorStep 0)
        (griessConwayEncode generatedFeasibleContainingZeroOutsideAnchorSource).2.2 =
          fun t j => ((0 : ℚ) : ℝ) / Real.sqrt 2
      rw [generatedFeasibleContainingZeroOutsideAnchorSource,
        generatedAxis_triality_octad_tensor_zero_all, map_zero, zero_tensor]

/-- Every actual outgoing matrix, short, and tensor coordinate is the complete forward packet. -/
theorem generatedFeasibleContainingZeroOutsideAnchorSecond_actual :
    griessConwayEncode (sExtra (rhoLocal
      (localFiberIntoH (generatedFeasibleContainingZeroOutsideAnchorStep 0))
        generatedFeasibleContainingZeroOutsideAnchorSource)) =
      generatedAxisGlobalRationalPacketReal generatedFeasibleContainingZeroOutsideAnchorSecondPacket := by
  rw [← generatedFeasibleContainingZeroOutsideAnchorTriality_packet]
  exact generatedAxisGlobalRationalTriality_of_actual _ _
    generatedFeasibleContainingZeroOutsideAnchorFirst_actual

/-- The explicit complete source action reaches the entire original containing octad axis. -/
theorem generatedFeasibleContainingZeroOutsideAnchorWhole_axis :
    rhoLocal (localFiberIntoH (generatedFeasibleContainingZeroOutsideAnchorStep 1))
      (sExtra (rhoLocal (localFiberIntoH (generatedFeasibleContainingZeroOutsideAnchorStep 0))
        generatedFeasibleContainingZeroOutsideAnchorSource)) =
          generatedFeasibleContainingZeroOutsideAnchorTarget := by
  apply (Function.LeftInverse.injective griessConwayDecode_encode)
  change griessConwayEncode (localGriessRepresentation
    (generatedFeasibleContainingZeroOutsideAnchorStep 1)
      (sExtra (rhoLocal (localFiberIntoH (generatedFeasibleContainingZeroOutsideAnchorStep 0))
        generatedFeasibleContainingZeroOutsideAnchorSource))) = _
  rw [localGriessRepresentation_encode, localConwayRawRepresentation_apply,
    generatedFeasibleContainingZeroOutsideAnchorSecond_actual]
  apply Prod.ext
  · change conwayMatrixAction (1 * co1XiIsometry)
        (generatedFeasibleContainingZeroOutsideAnchorMatrix2Q.map (Rat.castHom ℝ)) =
          (griessConwayEncode generatedFeasibleContainingZeroOutsideAnchorTarget).1
    rw [one_mul, xi_matrix_action, generatedFeasibleContainingZeroOutsideAnchorMatrix_target,
      target_matrix]
  · apply Prod.ext
    · change localShortOperator (generatedFeasibleContainingZeroOutsideAnchorStep 1)
        (fun r => (generatedFeasibleContainingZeroOutsideAnchorShortQ 2 r : ℝ)) =
          (griessConwayEncode generatedFeasibleContainingZeroOutsideAnchorTarget).2.1
      rw [generatedFeasibleContainingZeroOutsideAnchorShortQ_sum 2, step_one_short, target_short]
    · change localTensorRepresentation (generatedFeasibleContainingZeroOutsideAnchorStep 1)
        (fun t j => ((0 : ℚ) : ℝ) / Real.sqrt 2) =
          (griessConwayEncode generatedFeasibleContainingZeroOutsideAnchorTarget).2.2
      rw [zero_tensor, map_zero, generatedFeasibleContainingZeroOutsideAnchorTarget,
        generatedAxis_triality_octad_tensor_zero_all]

/-- Each entire actual corrected-Xi step fixes the genuine positive first axis1−2. -/
theorem generatedFeasibleContainingZeroOutsideAnchorStep_first (t : Fin 2) :
    rhoLocal (localFiberIntoH (generatedFeasibleContainingZeroOutsideAnchorStep t))
      (conwayShortAxis (Sum.inl (0, (23 : Fin 276))) 0) =
        conwayShortAxis (Sum.inl (0, (23 : Fin 276))) 0 := by
  have hq : spinConjugation (generatedFeasibleContainingZeroOutsideAnchorStep t).val.1
      (griessShortQ (Sum.inl (0, (23 : Fin 276)))) =
        qCentral 0 * griessShortQ (Sum.inl (0, (23 : Fin 276))) := by
    rw [generatedFeasibleContainingZeroOutsideAnchorQImage_actual, show qCentral 0 = 1 from rfl, one_mul]
    have h := generatedFeasibleContainingZeroOutsideAnchorFirst_Q t
    rw [generatedFeasibleContainingZeroOutsideAnchorQ_actual] at h
    exact h
  have hb := generatedFeasibleContainingZeroSparseShort_basis
    (generatedFeasibleContainingZeroOutsideAnchorStep t) _ _ 0 hq
  rw [qSign_zero, one_smul] at hb
  have hs : localShortRepresentation (generatedFeasibleContainingZeroOutsideAnchorStep t)
      ((-8 : ℝ) • Pi.single (Sum.inl (0, (23 : Fin 276))) 1) =
        (-8 : ℝ) • Pi.single (Sum.inl (0, (23 : Fin 276))) 1 := by
    change localShortOperator _ _ = _
    rw [map_smul, hb]
  rw [conwayShortAxis_pair_zero]
  change localGriessRepresentation (generatedFeasibleContainingZeroOutsideAnchorStep t)
    (conwayAxis 23) = conwayAxis 23
  exact (localAxis_fiber_fixed_iff _ _).mpr ((localAxis_short_fixed_iff _ _).mp hs)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
