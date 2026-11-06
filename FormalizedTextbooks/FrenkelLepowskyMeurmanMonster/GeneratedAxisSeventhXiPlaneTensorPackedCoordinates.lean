/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneTensorPackedCertificates

/-! The packed evaluator is the entire original tensor, with every preferred-source sign. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency true

/-- The three packed odd slots equal every complete original middle odd coefficient. -/
theorem generatedSeventhXiTensorOddCache_eq (d : Fin 2048) (i : Fin 24) :
    generatedSeventhXiTensorOddCache d i = generatedSeventhXiOddSparseCache d i := by
  unfold generatedSeventhXiTensorOddCache generatedSeventhXiOddSparseCache
  split_ifs with h
  · apply Finset.sum_congr rfl
    intro k _
    rw [(generatedSeventhXiTensorPacked_odd_slots _ k).1,
      (generatedSeventhXiTensorPacked_odd_slots _ k).2]
  · rfl

/-- The entire canonical tensor numerator uses the complete verified compact coefficient tables. -/
def generatedSeventhXiPlaneTensorPacked (d : Fin 4096) (i : Fin 24) : ℤ :=
  let c := generatedSeventhXiTensorLow d
  (if (generatedSeventhXiTensorMask c).testBit i.val then -1 else 1) *
    ((if d.val.testBit 11 then -1 else 1) * 8 * generatedSeventhXiTensorOddCache c i -
      generatedSeventhXiTensorKappa c * generatedSeventhXiTensorFrame i *
        (generatedSeventhXiTensorSpin ⟨c.val, by omega⟩ -
          generatedSeventhXiTensorSpin ⟨c.val + 2048, by omega⟩))

/-- Every packed tensor coefficient equals its complete original signed numerator. -/
theorem generatedSeventhXiPlaneTensorPacked_eq (d : Fin 4096) (i : Fin 24) :
    generatedSeventhXiPlaneTensorPacked d i = generatedSeventhXiPlaneTensorSparse d i := by
  have hs : nortonUIntegerSign (golayLabelCoefficients d 11) =
      (if d.val.testBit 11 then -1 else 1) := by
    cases h : d.val.testBit 11 <;> simp [golayLabelCoefficients, nortonUIntegerSign, h]
  simp only [generatedSeventhXiPlaneTensorPacked, generatedSeventhXiPlaneTensorSparse,
    generatedSeventhXiTensorPacked_mask, generatedSeventhXiTensorOddCache_eq,
    generatedSeventhXiTensorPacked_kappa, generatedSeventhXiTensorPacked_spin,
    generatedSeventhXiTensorPacked_frame, hs]

/-- The packed evaluator retains every coordinate of the genuine canonical tensor. -/
theorem generatedSeventhXiPlaneTensorPacked_actual (t : SpinIndex) (i : Fin 24) :
    (griessConwayEncode generatedSeventhXiPlaneCanonicalAxis).2.2 t i =
      (generatedSeventhXiPlaneTensorPacked (nortonUIntegerLabel t) i : ℝ) /
        (32 * Real.sqrt 2) := by
  rw [generatedSeventhXiPlaneTensorPacked_eq]
  exact generatedSeventhXiPlaneTensorSparse_actual t i

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
