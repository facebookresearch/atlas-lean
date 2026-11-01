/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthTensor
@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Original triality has zero odd-short output whenever its input tensor block is zero. -/
theorem generatedFourthQShortBasis_triality_odd_zero (x : GriessSpace)
    (ht : (griessConwayEncode x).2.2 = 0) (d : Fin 2048) (i : Fin 24) :
    (griessConwayEncode (sExtra x)).2.1 (Sum.inr (Sum.inr (d, i))) = 0 := by
  have hc : trialityCycle.symm 0 = 2 := by decide
  have h (y : ConwayRawSpace) (hy : y.2.2 = 0) :
      (griessConwayEncode (sExtra (griessConwayDecode y))).2.1
        (Sum.inr (Sum.inr (d, i))) = 0 := by
    simp [griessConwayDecode, griessConwayEncode, sExtra, griessTriality,
      trialityBlockAction, trialityCycleAction, hc, hy]
  simpa only [griessConwayDecode_encode] using h (griessConwayEncode x) ht

/-- Every actual odd-short coefficient of the fourth axis is zero. -/
theorem generatedFourthQShortBasis_odd_zero (d : Fin 2048) (i : Fin 24) :
    (griessConwayEncode generatedFourthAxis).2.1 (Sum.inr (Sum.inr (d, i))) = 0 := by
  rw [generatedFourthAxis_local_expression]
  exact generatedFourthQShortBasis_triality_odd_zero _ generatedFourth_middle_tensor_zero d i

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
