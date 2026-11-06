/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthInverseSpatial

/-! The one nonzero original pair-short coordinate before the final triality.
The result follows from actual physical support and the verified full-Q image. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The inverse preferred-Q certificate determines the original forward short row. -/
theorem generatedFourth_pair_forward_operator (X : GriessShortIndex → ℝ) :
    localShortOperator generatedFourthLocalFiber X generatedFourthPairInput =
      qSign generatedFourthPairPhase * X generatedFourthPairOutput := by
  have h := monsterNortonShortOperator_of_Q_image _ _ _ _ generatedFourth_pair_image
    (localShortOperator generatedFourthLocalFiber X)
  have hc : localShortOperator generatedFourthLocalFiber⁻¹
      (localShortOperator generatedFourthLocalFiber X) = X := by
    change (localShortOperator generatedFourthLocalFiber⁻¹).comp
      (localShortOperator generatedFourthLocalFiber) X = X
    rw [← localShortOperator_mul, inv_mul_cancel, localShortOperator_one]
    rfl
  rw [hc] at h
  calc
    _ = qSign generatedFourthPairPhase *
        (qSign generatedFourthPairPhase *
          localShortOperator generatedFourthLocalFiber X generatedFourthPairInput) := by
      rw [← mul_assoc, qSign_sq, one_mul]
    _ = _ := by rw [← h]

/-- The preferred output row in the original unsigned octad transition is minus one. -/
theorem generatedFourth_original_pair_output :
    (griessConwayEncode (sExtra (conwayShortAxis
      (Sum.inr (Sum.inl (generatedFourthOctad, 0))) 0))).2.1
        generatedFourthPairOutput = -1 := by
  have hm : griessOctadSignMask generatedFourthOctad 0 = 0 := by
    simp [griessOctadSignMask, show trialityEvenMask 0 = 0 from by decide]
  unfold generatedFourthPairOutput
  rw [generatedAxis_triality_octad_pair_coordinate,
    generatedFourthPairOutput_coordinates]
  have hs : Real.sqrt 8 * Real.sqrt 8 = 8 := Real.mul_self_sqrt (by norm_num)
  have h10 : Nat.testBit 0xcccc00 10 = true := by decide
  have h11 : Nat.testBit 0xcccc00 11 = true := by decide
  have hv (i : Fin 24) (hi : Nat.testBit 0xcccc00 i.val = true) :
      griessShortVector (Sum.inr (Sum.inl (generatedFourthOctad, 0))) i = 2 / Real.sqrt 8 := by
    simp only [griessShortVector, griessShortIntegral, generatedFourthOctad_mask, hm,
      Nat.zero_testBit, hi]
    norm_num
  rw [hv 10 h10, hv 11 h11]
  simp only [show (1 : Fin 2) ≠ 0 from by decide, ite_false]
  have hsqrt : Real.sqrt 8 ≠ 0 := by positivity
  field_simp
  nlinarith [hs]

/-- The actual local transition row has the genuine full-Q phase and no unknown scale. -/
theorem generatedFourth_transported_pair_input :
    localShortOperator generatedFourthLocalFiber
      (griessConwayEncode (sExtra (conwayShortAxis
        (Sum.inr (Sum.inl (generatedFourthOctad, 0))) 0))).2.1
          generatedFourthPairInput = -qSign generatedFourthPairPhase := by
  rw [generatedFourth_pair_forward_operator, generatedFourth_original_pair_output]
  ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
