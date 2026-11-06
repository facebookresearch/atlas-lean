/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthFinalTensorPacked

/-! The final odd-short rows come from the entire incoming Z tensor coordinate. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Original triality sends the incoming Z row, with its normalization and sign, to odd shorts. -/
theorem generatedSixth_triality_odd_coordinate (x : GriessSpace)
    (d : Fin 2048) (j : Fin 24) :
    (griessConwayEncode (sExtra x)).2.1 (Sum.inr (Sum.inr (d, j))) =
      qSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) *
        ((griessConwayEncode x).2.2 (golayLabelCoefficients ⟨d.val, by omega⟩) j +
          (griessConwayEncode x).2.2
            (golayLabelCoefficients ⟨d.val + 2048, by omega⟩) j) / Real.sqrt 2 := by
  have h0 : trialityCycle.symm 0 = 2 := by decide
  simp [griessConwayEncode, sExtra, griessTriality, trialityBlockAction,
    trialityCycleAction, h0]
  have hn : Real.sqrt 2 ≠ 0 := by positivity
  have hp : qSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) ^ 2 = 1 := by
    simpa only [pow_two] using qSign_sq
      (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ)
  split_ifs <;> field_simp [hn] <;> ring_nf <;>
    norm_num [hp, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

/-- The complete integer numerator of a final preferred odd-short coordinate. -/
def generatedSixthFinalOddNumerator (d : Fin 2048) (j : Fin 24) : ℤ :=
  -nortonUIntegerSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) *
    generatedSixthFrameVectorData 8 0 j *
      (generatedSixthPackedSpinPhase ⟨d.val, by omega⟩ +
        generatedSixthPackedSpinPhase ⟨d.val + 2048, by omega⟩)

/-- Every actual final odd-short coefficient equals its complete original integer value over 32. -/
theorem generatedSixth_final_odd_coordinate (d : Fin 2048) (j : Fin 24) :
    (griessConwayEncode generatedSixthAxis).2.1 (Sum.inr (Sum.inr (d, j))) =
      (generatedSixthFinalOddNumerator d j : ℝ) / 32 := by
  rw [generatedSixthAxis_local_expression, generatedSixth_triality_odd_coordinate,
    generatedSixth_middle_tensor_integer, generatedSixth_middle_tensor_integer,
    nortonUIntegerLabel_coeff, nortonUIntegerLabel_coeff,
    generatedSixth_spin_numerator_phase, generatedSixth_spin_numerator_phase,
    ← generatedSixth_packed_spin_phase, ← generatedSixth_packed_spin_phase]
  simp only [generatedSixthFinalOddNumerator, Int.cast_mul, Int.cast_neg,
    Int.cast_add, nortonUIntegerSign_real]
  have hn : Real.sqrt 2 ≠ 0 := by positivity
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  field_simp [hn]
  rw [hs]
  ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
