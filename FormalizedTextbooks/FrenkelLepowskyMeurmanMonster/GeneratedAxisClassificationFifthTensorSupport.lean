/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthTensor

/-! Exact support of each original physical spin column of the fifth prototype. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The incident original Y dictionary coefficient is always a nonzero real number. -/
theorem generatedFifth_Y_incident_ne_zero (t : SpinIndex) (i : Fin 24) :
    trialityYTensor (spinDictionaryCode t) i t i ≠ 0 := by
  have hq : qSign (t 11) ≠ 0 := by
    intro hz
    have hh := qSign_sq (t 11)
    rw [hz] at hh
    norm_num at hh
  have hs : (if (golayEncodedMask (spinDictionaryCode t).val).testBit i.val
      then (-1 : ℝ) else 1) ≠ 0 := by
    split_ifs <;> norm_num
  simpa only [trialityYTensor, ite_true, mul_one] using
    div_ne_zero (mul_ne_zero hq hs) (show Real.sqrt 2 ≠ 0 by positivity)

/-- A spin coordinate is nonzero exactly on one of the 64 genuine dictionary entries. -/
theorem generatedFifth_tensor_nonzero_iff (t : SpinIndex) (i : Fin 24) :
    (griessConwayEncode generatedFifthAxis).2.2 t i ≠ 0 ↔
      ∃ j : Fin 64, generatedFifthOddRootOutputData j = (spinDictionaryCode t, i) := by
  rw [generatedFifthAxis_local_expression,
    generatedFourthQ_triality_tensor_coordinate _ generatedFifth_middle_tensor_zero]
  rw [mul_ne_zero_iff]
  rw [and_iff_left (generatedFifth_Y_incident_ne_zero t i)]
  rw [generatedFourth_local_short]
  exact generatedFifth_odd_middle_nonzero_iff _ _

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
