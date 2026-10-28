/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightIncomingPositiveTensorInteger
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthFinalPairTriality
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthFinalOddTriality
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.TrialityOrder

/-! Complete signed short coordinates of the actual positive final axis. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-- The full original incoming matrix numerator, using all twenty-four genuine frame columns. -/
def generatedRootEightIncomingMatrixNumerator (i j : Fin 24) : ℤ :=
  ∑ t : Fin 24, (if Nat.testBit 0x0f000f t.val then 2 else 1) *
    generatedFifthRootEightFrameData 7 t i * generatedFifthRootEightFrameData 7 t j

/-- Every actual incoming matrix coordinate has its complete integer normalization. -/
theorem generatedRootEight_incoming_positive_matrix_integer (i j : Fin 24) :
    (griessConwayEncode generatedRootEightIncomingPositiveDestination).1 i j =
      (generatedRootEightIncomingMatrixNumerator i j : ℝ) / 256 := by
  rw [generatedRootEight_incoming_positive_matrix_short.1,
    ← generatedAxisGlobalFifthRoot08Packet_actual,
    generatedAxisGlobalFifthShortWord_matrix_entry]
  change (∑ t : Fin 24, generatedAxisGlobalFifthMatrixDiagonal t *
    leechIsomMatrix (generatedAxisGlobalFifthShortSpatialWord 8)⁻¹ t i *
    leechIsomMatrix (generatedAxisGlobalFifthShortSpatialWord 8)⁻¹ t j) = _
  simp_rw [generatedFifthRootEight_inverse_matrix_coordinate]
  simp only [generatedRootEightIncomingMatrixNumerator, Int.cast_sum,
    Int.cast_mul, Int.cast_ite, Int.cast_ofNat, Int.cast_one, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro t _
  unfold generatedAxisGlobalFifthMatrixDiagonal
  split_ifs <;> ring

/-- Every short-family numerator after the actual positive triality, including all zero entries. -/
def generatedRootEightPositiveFinalShortNumerator : GriessShortIndex → ℤ
  | Sum.inl (s, p) =>
      8 * (generatedFifthRootEightShortCachedCoefficient (Sum.inl (0, p)) -
        generatedFifthRootEightShortCachedCoefficient (Sum.inl (1, p))) +
      (if s = 0 then 1 else -1) * generatedRootEightIncomingMatrixNumerator
        (griessCoordinatePair p).1 (griessCoordinatePair p).2
  | Sum.inr (Sum.inl (o, e)) =>
      2 * ∑ f : Fin 64, trialityIntegerMatrix e f *
        generatedFifthRootEightShortCachedCoefficient (Sum.inr (Sum.inl (o, f)))
  | Sum.inr (Sum.inr (d, i)) =>
      2 * (if ((golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) : ZMod 2) = 0 then 1 else -1) *
        (generatedRootEightIncomingPositiveTensorNumerator ⟨d.val, by omega⟩ i +
          generatedRootEightIncomingPositiveTensorNumerator ⟨d.val + 2048, by omega⟩ i)

/-- The complete genuine positive final short block equals its integer formula over 256. -/
theorem generatedRootEight_positive_final_short_integer (r : GriessShortIndex) :
    (griessConwayEncode generatedRootEightIncomingPositiveTrialityDestination).2.1 r =
      (generatedRootEightPositiveFinalShortNumerator r : ℝ) / 256 := by
  rcases r with ⟨s, p⟩ | (⟨o, e⟩ | ⟨d, i⟩)
  · rw [generatedRootEightIncomingPositiveTrialityDestination,
      generatedNinth_final_triality_pair_coordinate]
    simp_rw [generatedRootEight_incoming_positive_short_integer,
      generatedRootEight_incoming_positive_matrix_integer]
    simp only [generatedRootEightPositiveFinalShortNumerator, Int.cast_add, Int.cast_mul,
      Int.cast_sub, Int.cast_ofNat, Int.cast_ite, Int.cast_neg, Int.cast_one]
    split_ifs <;> ring
  · rw [generatedRootEightIncomingPositiveTrialityDestination,
      monsterNortonTensor_extra_octad_coordinates, trialityOctadAction_matrix]
    simp_rw [generatedRootEight_incoming_positive_short_integer]
    simp only [trialityRealMatrix, Matrix.mulVec, dotProduct, Matrix.smul_apply,
      Matrix.map_apply, generatedRootEightPositiveFinalShortNumerator,
      Int.cast_mul, Int.cast_ofNat, Int.cast_sum, smul_eq_mul]
    rw [Finset.mul_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro f _
    change (1 / 8 : ℝ) * (trialityIntegerMatrix e f : ℝ) *
      ((generatedFifthRootEightShortCachedCoefficient (Sum.inr (Sum.inl (o, f))) : ℝ) / 16) =
      (2 * ((trialityIntegerMatrix e f : ℝ) *
        (generatedFifthRootEightShortCachedCoefficient (Sum.inr (Sum.inl (o, f))) : ℝ))) / 256
    ring
  · rw [generatedRootEightIncomingPositiveTrialityDestination,
      generatedNinth_final_triality_odd_coordinate]
    simp_rw [generatedRootEight_incoming_positive_tensor_integer]
    simp only [nortonUIntegerLabel_coeff, generatedRootEightPositiveFinalShortNumerator,
      Int.cast_mul, Int.cast_add, Int.cast_ofNat, Int.cast_ite, Int.cast_neg, Int.cast_one, qSign]
    have hs : Real.sqrt 2 ≠ 0 := by positivity
    have hss : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by positivity)
    split_ifs <;> field_simp [hs] <;> simp only [pow_two, hss] <;> ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
