/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact integer tensor coordinates at the actual eleventh first-line word step. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01SeventhUCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01SeventhUShortInteger
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsTensorInverseTrialityFullTensor

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem dictionary_code_label (n : Fin 4096) :
    spinDictionaryCode (golayLabelCoefficients n) =
      (⟨n.val % 2048, Nat.mod_lt _ (by norm_num)⟩ : Fin 2048) := by
  apply Fin.ext
  simp only [spinDictionaryCode, spinDictionaryLabel_coeff]

/-- The complete integer tensor numerator after the actual eleventh inverse-triality step. -/
def monsterNortonLine01EleventhTensorIntegerNumerator (n : Fin 4096) (i : Fin 24) : ℤ :=
  let d : Fin 2048 := ⟨n.val % 2048, Nat.mod_lt _ (by norm_num)⟩
  nortonUIntegerSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) *
    (monsterNortonLine01SeventhUShortIntegerNumerator (Sum.inr (Sum.inr (d, i))) +
      nortonUIntegerSign (golayLabelCoefficients n 11) *
        (if (golayEncodedMask d.val).testBit i.val then (-1 : ℤ) else 1) *
          (monsterNortonLine01SeventhUTensorIntegerNumerator ⟨d.val, by omega⟩ i +
            monsterNortonLine01SeventhUTensorIntegerNumerator ⟨d.val + 2048, by omega⟩ i))

private theorem inverse_tensor_scalar (p s a x u v : ℝ) :
    (p * ((1 / 512) * x) + s * a *
      (p * ((1 / (256 * Real.sqrt 2)) * u +
        (1 / (256 * Real.sqrt 2)) * v) / Real.sqrt 2)) / Real.sqrt 2 =
          (1 / (512 * Real.sqrt 2)) * (p * (x + s * a * (u + v))) := by
  have hs : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hs2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  field_simp
  ring_nf
  rw [hs2]
  ring

/-- Every actual eleventh tensor coordinate has its exact integer numerator and scale. -/
theorem monsterNortonLine01EleventhTensorInteger_actual (n : Fin 4096) (i : Fin 24) :
    (griessConwayEncode (sExtra.symm (y555NortonActualU.val
      (sExtra monsterNortonLine01TensorAfterVUExtraInverseVInverseUV)))).2.2
        (golayLabelCoefficients n) i =
          (1 / (512 * Real.sqrt 2) : ℝ) *
            (monsterNortonLine01EleventhTensorIntegerNumerator n i : ℝ) := by
  rw [monsterNortonTensorInverseTrialityCoordinates_actual]
  simp only [monsterNortonTensorInverseTrialityCoordinates, dictionary_code_label,
    monsterNortonLine01SeventhUTensorInteger_actual]
  rw [monsterNortonLine01SeventhU_encode]
  dsimp only
  rw [monsterNortonLine01SeventhUShortInteger_actual]
  simp only [monsterNortonLine01EleventhTensorIntegerNumerator, Int.cast_mul, Int.cast_add,
    Int.cast_ite, Int.cast_neg, Int.cast_one, nortonUIntegerSign_real]
  exact inverse_tensor_scalar _ _ _ _ _ _

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
