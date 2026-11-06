/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual inverse triality in the original physical tensor and odd-short coordinates. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsTensorTrialityCoordinates

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Inverse triality rotates each actual XYZ coordinate in the opposite direction. -/
theorem monsterNortonTensor_inverse_XYZ (x : GriessSpace) (s : Fin 3) (k : Fin 49152) :
    (trialityBlocksEquiv (sExtra.symm x)).2.2.2 s k =
      (trialityBlocksEquiv x).2.2.2 (trialityCycle s) k := by
  have h := monsterTriality_XYZ_blocks (sExtra.symm x) (trialityCycle s) k
  rw [LinearEquiv.apply_symm_apply, Equiv.symm_apply_apply] at h
  exact h.symm

/-- The inverse-triality odd-short row is the old signed low/high tensor difference. -/
theorem monsterNortonTensor_extra_inverse_odd (x : GriessSpace) (d : Fin 2048) (i : Fin 24) :
    (griessConwayEncode (sExtra.symm x)).2.1 (Sum.inr (Sum.inr (d, i))) =
      (if (golayEncodedMask d.val).testBit i.val then (-1 : ℝ) else 1) *
        ((griessConwayEncode x).2.2 (golayLabelCoefficients ⟨d.val, by omega⟩) i -
          (griessConwayEncode x).2.2
            (golayLabelCoefficients ⟨d.val + 2048, by omega⟩) i) / Real.sqrt 2 := by
  change (trialityBlocksEquiv (sExtra.symm x)).2.2.2 0 (finProdFinEquiv (d, i)) = _
  rw [monsterNortonTensor_inverse_XYZ, show trialityCycle 0 = 1 by decide,
    monsterNortonTensor_dictionary_Y]

/-- The low physical row after inverse triality receives the old X and Z dictionary rows. -/
theorem monsterNortonTensor_extra_inverse_low
    (x : GriessSpace) (d : Fin 2048) (i : Fin 24) :
    (griessConwayEncode (sExtra.symm x)).2.2 (golayLabelCoefficients ⟨d.val, by omega⟩) i =
      (qSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) *
          (griessConwayEncode x).2.1 (Sum.inr (Sum.inr (d, i))) +
        (if (golayEncodedMask d.val).testBit i.val then (-1 : ℝ) else 1) *
          (trialityBlocksEquiv x).2.2.2 2 (finProdFinEquiv (d, i))) / Real.sqrt 2 := by
  change (qSign _ * (trialityBlocksEquiv (sExtra.symm x)).2.2.2 2 _ +
    qSign (golayLabelCoefficients ⟨d.val, by omega⟩ 11) * _ *
      (trialityBlocksEquiv (sExtra.symm x)).2.2.2 1 _) / _ = _
  rw [spinDictionaryCode_low, golayLabel_low_last, qSign_zero, one_mul,
    monsterNortonTensor_inverse_XYZ, monsterNortonTensor_inverse_XYZ,
    show trialityCycle 2 = 0 by decide, show trialityCycle 1 = 2 by decide]
  rfl

/-- The high physical row after inverse triality has the opposite old Z contribution. -/
theorem monsterNortonTensor_extra_inverse_high
    (x : GriessSpace) (d : Fin 2048) (i : Fin 24) :
    (griessConwayEncode (sExtra.symm x)).2.2
        (golayLabelCoefficients ⟨d.val + 2048, by omega⟩) i =
      (qSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) *
          (griessConwayEncode x).2.1 (Sum.inr (Sum.inr (d, i))) -
        (if (golayEncodedMask d.val).testBit i.val then (-1 : ℝ) else 1) *
          (trialityBlocksEquiv x).2.2.2 2 (finProdFinEquiv (d, i))) / Real.sqrt 2 := by
  change (qSign _ * (trialityBlocksEquiv (sExtra.symm x)).2.2.2 2 _ +
    qSign (golayLabelCoefficients ⟨d.val + 2048, by omega⟩ 11) * _ *
      (trialityBlocksEquiv (sExtra.symm x)).2.2.2 1 _) / _ = _
  rw [spinDictionaryCode_high, golayLabel_high_last, qSign_one, neg_one_mul,
    monsterNortonTensor_inverse_XYZ, monsterNortonTensor_inverse_XYZ,
    show trialityCycle 2 = 0 by decide, show trialityCycle 1 = 2 by decide]
  simp only [neg_mul, sub_eq_add_neg]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
