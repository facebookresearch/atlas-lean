/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneOddSparseCache
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneTensorNumerator

/-! A small exact arithmetic evaluator for every coordinate of the canonical tensor. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency true

/-- Each tensor coordinate uses the complete verified three-slot odd coefficient cache. -/
def generatedSeventhXiPlaneTensorSparse (d : Fin 4096) (i : Fin 24) : ℤ :=
  let c := generatedSeventhXiTensorLow d
  (if (golayEncodedMask c.val).testBit i.val then -1 else 1) *
    (nortonUIntegerSign (golayLabelCoefficients d 11) * 8 *
        generatedSeventhXiOddSparseCache c i -
      nortonUIntegerSign (golayMaskWeight (golayEncodedMask c.val) / 4 : ℕ) *
        generatedSeventhFrameVectorData 7 0 i *
        (generatedSeventhXiPlaneSpinInteger ⟨c.val, by omega⟩ -
          generatedSeventhXiPlaneSpinInteger ⟨c.val + 2048, by omega⟩))

/-- The small evaluator is exactly the original full tensor numerator at every label. -/
theorem generatedSeventhXiPlaneTensorSparse_eq (d : Fin 4096) (i : Fin 24) :
    generatedSeventhXiPlaneTensorSparse d i = generatedSeventhXiPlaneTensorNumerator d i := by
  simp only [generatedSeventhXiPlaneTensorSparse, generatedSeventhXiPlaneTensorNumerator,
    generatedSeventhXiOddSparseCache_eq]

/-- The evaluator retains the complete genuine canonical tensor, including all signs. -/
theorem generatedSeventhXiPlaneTensorSparse_actual (t : SpinIndex) (i : Fin 24) :
    (griessConwayEncode generatedSeventhXiPlaneCanonicalAxis).2.2 t i =
      (generatedSeventhXiPlaneTensorSparse (nortonUIntegerLabel t) i : ℝ) /
        (32 * Real.sqrt 2) := by
  rw [generatedSeventhXiPlaneTensorSparse_eq]
  exact generatedSeventhXiPlaneTensorNumerator_actual t i

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
