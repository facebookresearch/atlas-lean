/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact integer physical coordinates for the entire seventh actual first-line tensor state. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01TensorSixthInteger
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01OddSixthCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsTensorTrialityFullCoordinates

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem dictionary_code_label (n : Fin 4096) :
    spinDictionaryCode (golayLabelCoefficients n) =
      (⟨n.val % 2048, Nat.mod_lt _ (by norm_num)⟩ : Fin 2048) := by
  apply Fin.ext
  simp only [spinDictionaryCode, spinDictionaryLabel_coeff]

private theorem triality_integer_algebra (p s l a b x : ℝ) :
    (p * (s * ((-1 / (2048 * Real.sqrt 2)) * a -
        (-1 / (2048 * Real.sqrt 2)) * b) / Real.sqrt 2) +
      l * s * ((1 / 64) * x)) / Real.sqrt 2 =
      (1 / (4096 * Real.sqrt 2)) * (s * (-p * (a - b) + 64 * l * x)) := by
  have hs : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hs2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  field_simp
  ring_nf
  rw [hs2]
  ring

/-- The exact integer tensor numerator after the actual positive-triality seventh word step. -/
def monsterNortonLine01TensorSeventhIntegerNumerator (n : Fin 4096) (i : Fin 24) : ℤ :=
  let d : Fin 2048 := ⟨n.val % 2048, Nat.mod_lt _ (by norm_num)⟩
  (if (golayEncodedMask d.val).testBit i.val then (-1 : ℤ) else 1) *
    (-nortonUIntegerSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) *
        (monsterNortonLine01TensorSixthIntegerNumerator ⟨d.val, by omega⟩ i -
          monsterNortonLine01TensorSixthIntegerNumerator ⟨d.val + 2048, by omega⟩ i) +
      64 * nortonUIntegerSign (golayLabelCoefficients n 11) *
        monsterNortonLine01OddSixthNumerator d i)

/-- Every actual seventh tensor coordinate is its exact integer divided by 4096 times sqrt two. -/
theorem monsterNortonLine01TensorSeventhInteger_actual (n : Fin 4096) (i : Fin 24) :
    (griessConwayEncode (sExtra monsterNortonLine01TensorAfterVUExtraInverseVInverseUV)).2.2
      (golayLabelCoefficients n) i =
        (1 / (4096 * Real.sqrt 2) : ℝ) *
          (monsterNortonLine01TensorSeventhIntegerNumerator n i : ℝ) := by
  rw [monsterNortonTensorTrialityCoordinates_actual]
  simp only [monsterNortonTensorTrialityCoordinates, dictionary_code_label,
    monsterNortonLine01TensorSixthInteger_actual, monsterNortonLine01OddSixth_coordinates,
    monsterNortonLine01TensorSeventhIntegerNumerator, Int.cast_mul, Int.cast_add,
    Int.cast_sub, Int.cast_neg, Int.cast_ite, Int.cast_one, Int.cast_ofNat,
    nortonUIntegerSign_real]
  exact triality_integer_algebra _ _ _ _ _ _

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
