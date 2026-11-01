/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual positive triality in the physical tensor coordinates. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsTensorAntisymmetricTriality

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The source Y row is the signed physical low/high tensor difference. -/
theorem monsterNortonTensor_dictionary_Y (x : GriessSpace) (d : Fin 2048) (i : Fin 24) :
    (trialityBlocksEquiv x).2.2.2 1 (finProdFinEquiv (d, i)) =
      (if (golayEncodedMask d.val).testBit i.val then (-1 : ℝ) else 1) *
        ((griessConwayEncode x).2.2 (golayLabelCoefficients ⟨d.val, by omega⟩) i -
          (griessConwayEncode x).2.2 (golayLabelCoefficients ⟨d.val + 2048, by omega⟩) i) /
            Real.sqrt 2 := by
  have h := congrArg (fun y : GriessSpace =>
    (trialityBlocksEquiv y).2.2.2 1 (finProdFinEquiv (d, i)))
    (griessConwayDecode_encode x)
  simpa only [griessConwayDecode, LinearEquiv.apply_symm_apply,
    Equiv.symm_apply_apply, show (1 : Fin 3) ≠ 0 by decide, ite_false, ite_true] using h.symm

/-- The low physical row after positive triality receives the old Y and odd-short rows. -/
theorem monsterNortonTensor_extra_low (x : GriessSpace) (d : Fin 2048) (i : Fin 24) :
    (griessConwayEncode (sExtra x)).2.2 (golayLabelCoefficients ⟨d.val, by omega⟩) i =
      (qSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) *
          (trialityBlocksEquiv x).2.2.2 1 (finProdFinEquiv (d, i)) +
        (if (golayEncodedMask d.val).testBit i.val then (-1 : ℝ) else 1) *
          (griessConwayEncode x).2.1 (Sum.inr (Sum.inr (d, i)))) / Real.sqrt 2 := by
  change (qSign _ * (trialityBlocksEquiv (sExtra x)).2.2.2 2 _ +
    qSign (golayLabelCoefficients ⟨d.val, by omega⟩ 11) * _ *
      (trialityBlocksEquiv (sExtra x)).2.2.2 1 _) / _ = _
  rw [spinDictionaryCode_low, golayLabel_low_last, qSign_zero, one_mul,
    monsterTriality_XYZ_blocks, monsterTriality_XYZ_blocks,
    show trialityCycle.symm 2 = 1 by decide,
    show trialityCycle.symm 1 = 0 by decide]
  rfl

/-- The high physical row after positive triality has the opposite odd-short contribution. -/
theorem monsterNortonTensor_extra_high (x : GriessSpace) (d : Fin 2048) (i : Fin 24) :
    (griessConwayEncode (sExtra x)).2.2 (golayLabelCoefficients ⟨d.val + 2048, by omega⟩) i =
      (qSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) *
          (trialityBlocksEquiv x).2.2.2 1 (finProdFinEquiv (d, i)) -
        (if (golayEncodedMask d.val).testBit i.val then (-1 : ℝ) else 1) *
          (griessConwayEncode x).2.1 (Sum.inr (Sum.inr (d, i)))) / Real.sqrt 2 := by
  change (qSign _ * (trialityBlocksEquiv (sExtra x)).2.2.2 2 _ +
    qSign (golayLabelCoefficients ⟨d.val + 2048, by omega⟩ 11) * _ *
      (trialityBlocksEquiv (sExtra x)).2.2.2 1 _) / _ = _
  rw [spinDictionaryCode_high, golayLabel_high_last, qSign_one, neg_one_mul,
    monsterTriality_XYZ_blocks, monsterTriality_XYZ_blocks,
    show trialityCycle.symm 2 = 1 by decide,
    show trialityCycle.symm 1 = 0 by decide]
  simp only [neg_mul, sub_eq_add_neg]
  rfl

/-- The complete low physical tensor row after positive triality in the original coordinates. -/
theorem monsterNortonTensor_extra_low_coordinates
    (x : GriessSpace) (d : Fin 2048) (i : Fin 24) :
    (griessConwayEncode (sExtra x)).2.2 (golayLabelCoefficients ⟨d.val, by omega⟩) i =
      (qSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) *
          ((if (golayEncodedMask d.val).testBit i.val then (-1 : ℝ) else 1) *
            ((griessConwayEncode x).2.2 (golayLabelCoefficients ⟨d.val, by omega⟩) i -
              (griessConwayEncode x).2.2
                (golayLabelCoefficients ⟨d.val + 2048, by omega⟩) i) / Real.sqrt 2) +
        (if (golayEncodedMask d.val).testBit i.val then (-1 : ℝ) else 1) *
          (griessConwayEncode x).2.1 (Sum.inr (Sum.inr (d, i)))) / Real.sqrt 2 := by
  rw [monsterNortonTensor_extra_low, monsterNortonTensor_dictionary_Y]

/-- The complete high physical tensor row after positive triality in the original coordinates. -/
theorem monsterNortonTensor_extra_high_coordinates
    (x : GriessSpace) (d : Fin 2048) (i : Fin 24) :
    (griessConwayEncode (sExtra x)).2.2
        (golayLabelCoefficients ⟨d.val + 2048, by omega⟩) i =
      (qSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) *
          ((if (golayEncodedMask d.val).testBit i.val then (-1 : ℝ) else 1) *
            ((griessConwayEncode x).2.2 (golayLabelCoefficients ⟨d.val, by omega⟩) i -
              (griessConwayEncode x).2.2
                (golayLabelCoefficients ⟨d.val + 2048, by omega⟩) i) / Real.sqrt 2) -
        (if (golayEncodedMask d.val).testBit i.val then (-1 : ℝ) else 1) *
          (griessConwayEncode x).2.1 (Sum.inr (Sum.inr (d, i)))) / Real.sqrt 2 := by
  rw [monsterNortonTensor_extra_high, monsterNortonTensor_dictionary_Y]

/-- Positive triality preserves each actual octad block and applies its original Fourier action. -/
theorem monsterNortonTensor_extra_octad_coordinates
    (x : GriessSpace) (d : Fin 759) (e : Fin 64) :
    (griessConwayEncode (sExtra x)).2.1 (Sum.inr (Sum.inl (d, e))) =
      trialityOctadAction (fun r => (griessConwayEncode x).2.1
        (Sum.inr (Sum.inl (d, r)))) e := by
  simp only [griessConwayEncode, sExtra, griessTriality, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply, trialityBlockAction, LinearEquiv.prodCongr_apply]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
