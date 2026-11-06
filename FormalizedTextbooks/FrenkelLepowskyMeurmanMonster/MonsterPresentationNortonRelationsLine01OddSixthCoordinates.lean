/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact computable odd-short coordinates at the sixth actual first-line word step. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01OctadSixthCoordinates

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem physical_slot_column (k : Fin 16) :
    monsterNortonLine01ShortPhysicalSlot (monsterNortonLine01ShortPhysicalColumn k) = k := by
  revert k
  decide +kernel

private theorem short_single_odd (a : Fin 64) (k : Fin 16) (d : Fin 2048) (i : Fin 24) :
    (Pi.single (monsterNortonLine01ShortInverseOutput a k) 1 : GriessShortIndex → ℤ)
      (Sum.inr (Sum.inr (d, i))) =
        if monsterNortonLine01ShortInverseIsOctad a = false ∧
            monsterNortonLine01ShortInverseOddCode a k = d ∧
            monsterNortonLine01ShortInverseOddCoordinate a k = i then 1 else 0 := by
  cases h : monsterNortonLine01ShortInverseIsOctad a <;>
    simp [monsterNortonLine01ShortInverseOutput, h, Pi.single_apply, eq_comm]

/-- The computable complete integer coordinate in each actual odd-short row. -/
def monsterNortonLine01OddSixthNumerator (d : Fin 2048) (i : Fin 24) : ℤ :=
  ∑ a : Fin 64, ∑ k : Fin 16,
    if monsterNortonLine01ShortInverseIsOctad a = false ∧
        monsterNortonLine01ShortInverseOddCode a k = d ∧
        monsterNortonLine01ShortInverseOddCoordinate a k = i then
      monsterNortonLine01ShortSixthSourceCoefficient a k else 0

/-- The finite odd-short formula is exactly the actual sixth integer numerator. -/
theorem monsterNortonLine01OddSixthNumerator_actual (d : Fin 2048) (i : Fin 24) :
    monsterNortonLine01ShortSixthIntegerNumerator (Sum.inr (Sum.inr (d, i))) =
      monsterNortonLine01OddSixthNumerator d i := by
  simp only [monsterNortonLine01ShortSixthIntegerNumerator, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, physical_slot_column, short_single_odd, mul_ite,
    mul_one, mul_zero, monsterNortonLine01OddSixthNumerator,
    monsterNortonLine01ShortSixthSourceCoefficient]

/-- Every actual sixth odd-short coordinate has its complete rational value. -/
theorem monsterNortonLine01OddSixth_coordinates (d : Fin 2048) (i : Fin 24) :
    (griessConwayEncode monsterNortonLine01TensorAfterVUExtraInverseVInverseUV).2.1
      (Sum.inr (Sum.inr (d, i))) = (1 / 64 : ℝ) *
        (monsterNortonLine01OddSixthNumerator d i : ℝ) := by
  change monsterNortonShortProjection monsterNortonLine01TensorAfterVUExtraInverseVInverseUV
    (Sum.inr (Sum.inr (d, i))) = _
  rw [monsterNortonLine01ShortSixthInteger_actual]
  simp only [Pi.smul_apply, smul_eq_mul, monsterNortonLine01OddSixthNumerator_actual]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
