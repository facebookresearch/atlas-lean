/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Specific physical-coordinate support of the sixth and seventh actual first-line states. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01TensorSixthInteger
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01OddSixthCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsTensorTrialityFullCoordinates

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual inverse physical columns used here vanish beyond coordinate fifteen. -/
theorem monsterNortonLine01InversePhysicalRow_zero (i : Fin 24) (k : Fin 16)
    (hi : 16 ≤ i.val) :
    monsterNortonUNumerator12 i (monsterNortonLine01ShortPhysicalColumn k) = 0 := by
  revert i k hi
  decide +kernel

/-- Every reached odd-short unit in this particular state has physical index below sixteen. -/
theorem monsterNortonLine01OddOutput_physical (a : Fin 64) (k : Fin 16)
    (h : monsterNortonLine01ShortInverseIsOctad a = false) :
    (monsterNortonLine01ShortInverseOddCoordinate a k).val < 16 := by
  revert a k h
  decide +kernel

/-- The actual sixth tensor numerator vanishes outside its sixteen physical coordinates. -/
theorem monsterNortonLine01TensorSixthInteger_physical_zero (n : Fin 4096) (i : Fin 24)
    (hi : 16 ≤ i.val) : monsterNortonLine01TensorSixthIntegerNumerator n i = 0 := by
  unfold monsterNortonLine01TensorSixthIntegerNumerator
  apply Finset.sum_eq_zero
  intro k _
  rw [monsterNortonLine01InversePhysicalRow_zero i k hi, mul_zero]

/-- The actual sixth odd-short numerator vanishes outside the same physical coordinates. -/
theorem monsterNortonLine01OddSixthInteger_physical_zero (d : Fin 2048) (i : Fin 24)
    (hi : 16 ≤ i.val) : monsterNortonLine01OddSixthNumerator d i = 0 := by
  unfold monsterNortonLine01OddSixthNumerator
  apply Finset.sum_eq_zero
  intro a _
  apply Finset.sum_eq_zero
  intro k _
  rw [ite_eq_right]
  rintro ⟨ha, _, he⟩
  have h := monsterNortonLine01OddOutput_physical a k ha
  rw [he] at h
  omega

/-- Every actual sixth physical tensor row beyond index fifteen is zero. -/
theorem monsterNortonLine01TensorSixth_physical_zero (n : Fin 4096) (i : Fin 24)
    (hi : 16 ≤ i.val) :
    (griessConwayEncode monsterNortonLine01TensorAfterVUExtraInverseVInverseUV).2.2
      (golayLabelCoefficients n) i = 0 := by
  rw [monsterNortonLine01TensorSixthInteger_actual,
    monsterNortonLine01TensorSixthInteger_physical_zero n i hi, Int.cast_zero, mul_zero]

/-- Every actual sixth odd-short row beyond physical index fifteen is zero. -/
theorem monsterNortonLine01OddSixth_physical_zero (d : Fin 2048) (i : Fin 24)
    (hi : 16 ≤ i.val) :
    (griessConwayEncode monsterNortonLine01TensorAfterVUExtraInverseVInverseUV).2.1
      (Sum.inr (Sum.inr (d, i))) = 0 := by
  rw [monsterNortonLine01OddSixth_coordinates,
    monsterNortonLine01OddSixthInteger_physical_zero d i hi, Int.cast_zero, mul_zero]

/-- The particular actual seventh tensor state is supported on the first sixteen physical rows. -/
theorem monsterNortonLine01TensorSeventh_physical_zero (t : SpinIndex) (i : Fin 24)
    (hi : 16 ≤ i.val) :
    (griessConwayEncode (sExtra monsterNortonLine01TensorAfterVUExtraInverseVInverseUV)).2.2
      t i = 0 := by
  rw [monsterNortonTensorTrialityCoordinates_actual]
  simp only [monsterNortonTensorTrialityCoordinates,
    monsterNortonLine01TensorSixth_physical_zero _ i hi,
    monsterNortonLine01OddSixth_physical_zero _ i hi,
    sub_zero, mul_zero, zero_div, add_zero]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
