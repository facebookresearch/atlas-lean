/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMiddleTensor
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFourthQTrialityTensor

/-! The outgoing tensor retains both original XYZ dictionary contributions. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Original triality mixes the incoming odd short row and the incoming Y tensor row. -/
private theorem triality_tensor_raw_coordinate (a : ConwayRawSpace)
    (t : SpinIndex) (j : Fin 24) :
    (griessConwayEncode (sExtra (griessConwayDecode a))).2.2 t j =
      a.2.1 (Sum.inr (Sum.inr (spinDictionaryCode t, j))) *
        trialityYTensor (spinDictionaryCode t) j t j +
      qSign (golayMaskWeight (golayEncodedMask (spinDictionaryCode t).val) / 4 : ℕ) *
        (if (golayEncodedMask (spinDictionaryCode t).val).testBit j.val then -1 else 1) *
        (a.2.2
          (golayLabelCoefficients ⟨(spinDictionaryCode t).val, by omega⟩) j -
        a.2.2
          (golayLabelCoefficients ⟨(spinDictionaryCode t).val + 2048, by omega⟩) j) / 2 := by
  have h1 : trialityCycle.symm 1 = 0 := by decide
  have h2 : trialityCycle.symm 2 = 1 := by decide
  simp [griessConwayEncode, sExtra, griessTriality, griessConwayDecode,
    trialityBlockAction, trialityCycleAction, h1, h2, trialityYTensor]
  have hn : Real.sqrt 2 ≠ 0 := by positivity
  split_ifs <;> field_simp [hn] <;> ring_nf <;>
    norm_num [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

/-- Original triality retains both the incoming odd-short row and its Y tensor row. -/
theorem generatedSixth_triality_tensor_coordinate (x : GriessSpace)
    (t : SpinIndex) (j : Fin 24) :
    (griessConwayEncode (sExtra x)).2.2 t j =
      (griessConwayEncode x).2.1 (Sum.inr (Sum.inr (spinDictionaryCode t, j))) *
        trialityYTensor (spinDictionaryCode t) j t j +
      qSign (golayMaskWeight (golayEncodedMask (spinDictionaryCode t).val) / 4 : ℕ) *
        (if (golayEncodedMask (spinDictionaryCode t).val).testBit j.val then -1 else 1) *
        ((griessConwayEncode x).2.2
          (golayLabelCoefficients ⟨(spinDictionaryCode t).val, by omega⟩) j -
        (griessConwayEncode x).2.2
          (golayLabelCoefficients ⟨(spinDictionaryCode t).val + 2048, by omega⟩) j) / 2 := by
  simpa only [griessConwayDecode_encode] using
    triality_tensor_raw_coordinate (griessConwayEncode x) t j

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
