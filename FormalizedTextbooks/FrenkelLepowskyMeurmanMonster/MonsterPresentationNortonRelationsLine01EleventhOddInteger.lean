/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact integer odd-short coordinates at the next actual inverse-triality word step. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01SeventhUCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsTensorInverseTrialityCoordinates

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The exact odd-short integer numerator after inverse triality in the literal line word. -/
def monsterNortonLine01EleventhOddIntegerNumerator (d : Fin 2048) (i : Fin 24) : ℤ :=
  (if (golayEncodedMask d.val).testBit i.val then (-1 : ℤ) else 1) *
    (monsterNortonLine01SeventhUTensorIntegerNumerator ⟨d.val, by omega⟩ i -
      monsterNortonLine01SeventhUTensorIntegerNumerator ⟨d.val + 2048, by omega⟩ i)

private theorem inverse_odd_scalar (s a b : ℝ) :
    s * ((1 / (256 * Real.sqrt 2)) * a -
      (1 / (256 * Real.sqrt 2)) * b) / Real.sqrt 2 =
        (1 / 512) * (s * (a - b)) := by
  have hs : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hs2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  field_simp
  ring_nf
  rw [hs2]
  ring

/-- Every actual next inverse-triality odd-short row has this exact integer numerator. -/
theorem monsterNortonLine01EleventhOddInteger_actual (d : Fin 2048) (i : Fin 24) :
    (griessConwayEncode (sExtra.symm (y555NortonActualU.val
      (sExtra monsterNortonLine01TensorAfterVUExtraInverseVInverseUV)))).2.1
        (Sum.inr (Sum.inr (d, i))) =
          (1 / 512 : ℝ) * (monsterNortonLine01EleventhOddIntegerNumerator d i : ℝ) := by
  rw [monsterNortonTensor_extra_inverse_odd, monsterNortonLine01SeventhUTensorInteger_actual,
    monsterNortonLine01SeventhUTensorInteger_actual]
  simp only [monsterNortonLine01EleventhOddIntegerNumerator, Int.cast_mul, Int.cast_sub,
    Int.cast_ite, Int.cast_neg, Int.cast_one]
  exact inverse_odd_scalar _ _ _

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
