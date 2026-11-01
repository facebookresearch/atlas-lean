/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The complete original coordinate dictionary of the actual tenth first-line word state. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01SeventhU
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01SeventhUCoordinateData

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The entire original coordinate vector after the genuine next Norton U word step. -/
theorem monsterNortonLine01SeventhU_encode :
    griessConwayEncode
      (y555NortonActualU.val (sExtra monsterNortonLine01TensorAfterVUExtraInverseVInverseUV)) =
        (0, (monsterNortonLine01SeventhUShortCoordinates,
          monsterNortonTensorProjection monsterNortonLine01TensorSeventhUVector)) := by
  rw [monsterNortonLine01SeventhU_actual, monsterNortonLine01SeventhU_candidate_encode]

/-- Every actual tenth-state tensor coordinate has its exact integer numerator. -/
theorem monsterNortonLine01SeventhUTensorInteger_actual (n : Fin 4096) (i : Fin 24) :
    (griessConwayEncode (y555NortonActualU.val
      (sExtra monsterNortonLine01TensorAfterVUExtraInverseVInverseUV))).2.2
        (golayLabelCoefficients n) i =
          (1 / (256 * Real.sqrt 2) : ℝ) *
            (monsterNortonLine01SeventhUTensorIntegerNumerator n i : ℝ) := by
  rw [monsterNortonLine01SeventhU_encode]
  exact monsterNortonLine01SeventhUTensorInteger_coordinates n i

private theorem short_outside_odd (r : GriessShortIndex)
    (hr : ∀ d i, r ≠ Sum.inr (Sum.inr (d, i))) :
    monsterNortonLine01SeventhUShortCoordinates r = 0 := by
  unfold monsterNortonLine01SeventhUShortCoordinates
  simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro j _
  apply Finset.sum_eq_zero
  intro p _
  rw [Pi.single_eq_of_ne (hr _ _), mul_zero, mul_zero]

/-- The actual tenth-state physical matrix is identically zero. -/
theorem monsterNortonLine01SeventhU_matrix_zero (i j : Fin 24) :
    (griessConwayEncode (y555NortonActualU.val
      (sExtra monsterNortonLine01TensorAfterVUExtraInverseVInverseUV))).1 i j = 0 := by
  rw [monsterNortonLine01SeventhU_encode]
  rfl

/-- The actual tenth-state pair-short coordinates vanish. -/
theorem monsterNortonLine01SeventhU_pair_zero (s : Fin 2) (p : Fin 276) :
    (griessConwayEncode (y555NortonActualU.val
      (sExtra monsterNortonLine01TensorAfterVUExtraInverseVInverseUV))).2.1
        (Sum.inl (s, p)) = 0 := by
  rw [monsterNortonLine01SeventhU_encode]
  exact short_outside_odd _ (by intro d i h; cases h)

/-- The actual tenth-state octad-short coordinates vanish. -/
theorem monsterNortonLine01SeventhU_octad_zero (d : Fin 759) (e : Fin 64) :
    (griessConwayEncode (y555NortonActualU.val
      (sExtra monsterNortonLine01TensorAfterVUExtraInverseVInverseUV))).2.1
        (Sum.inr (Sum.inl (d, e))) = 0 := by
  rw [monsterNortonLine01SeventhU_encode]
  exact short_outside_odd _ (by intro a i h; injection h with hi; cases hi)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
