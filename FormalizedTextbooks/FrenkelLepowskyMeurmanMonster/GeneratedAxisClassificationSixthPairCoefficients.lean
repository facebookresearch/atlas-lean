/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthPairData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOddShortCoordinates

/-! Three exact original third-axis coefficients, before the authentic local word. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The three selected original preferred-minus-pair rows retain their genuine signs. -/
theorem generatedSixth_source_pair_coefficient (j : Fin 3) :
    (griessConwayEncode generatedOddAxis).2.1 (Sum.inl (0, generatedSixthSourcePair j)) =
      if j = 0 then 1 / 4 else -3 / 4 := by
  have hs : Real.sqrt 8 * Real.sqrt 8 = 8 := Real.mul_self_sqrt (by norm_num)
  have hm : golayEncodedMask 0 = 0 := by decide +kernel
  rw [generatedOddAxis, generatedAxis_triality_odd_pair_coordinate,
    (generatedSixth_pair_coordinate_certificate j).1]
  simp only [griessShortVector, griessShortIntegral, Fin.val_zero, hm,
    Nat.zero_testBit, Bool.false_eq_true, ite_false, ite_true]
  fin_cases j <;> norm_num <;> field_simp <;> nlinarith only [hs]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
