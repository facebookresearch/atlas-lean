/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneCanonicalCoordinates

/-! A catalogue-free arithmetic formula for every original middle odd-short coefficient. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency true

/-- The actual checked descriptor selects an odd coordinate exactly by its code and position. -/
theorem generatedSeventhXiShortOutputLabel_odd_iff (s : Fin 2) (p : Fin 276)
    (d : Fin 2048) (i : Fin 24) :
    Sum.inr (Sum.inr (d, i)) = generatedSeventhXiShortOutputLabel s p ↔
      generatedSeventhXiShortDescriptor s p 0 ≠ 0 ∧
      generatedSeventhXiShortDescriptor s p 0 ≠ 1 ∧
      generatedSeventhXiShortDescriptor s p 1 = d.val ∧
      generatedSeventhXiShortDescriptor s p 2 = i.val := by
  by_cases h0 : generatedSeventhXiShortDescriptor s p 0 = 0
  · simp [generatedSeventhXiShortOutputLabel, h0]
  · by_cases h1 : generatedSeventhXiShortDescriptor s p 0 = 1
    · simp [generatedSeventhXiShortOutputLabel, h1]
    · simp [generatedSeventhXiShortOutputLabel, h0, h1,
        Fin.ext_iff, eq_comm]

/-- The finite formula uses the checked physical descriptor and genuine central bits. -/
def generatedSeventhXiMiddleOddNumerator (d : Fin 2048) (i : Fin 24) : ℤ :=
  ∑ s : Fin 2, ∑ p : Fin 276,
    generatedSeventhXiShortInputWeight s p *
      nortonUIntegerSign (generatedSeventhXiShortPhaseBit s p : ZMod 2) *
      (if generatedSeventhXiShortDescriptor s p 0 ≠ 0 ∧
          generatedSeventhXiShortDescriptor s p 0 ≠ 1 ∧
          generatedSeventhXiShortDescriptor s p 1 = d.val ∧
          generatedSeventhXiShortDescriptor s p 2 = i.val then 1 else 0)

/-- The catalogue-free arithmetic sum equals the complete genuine preferred-label numerator. -/
theorem generatedSeventhXiMiddleOddNumerator_eq (d : Fin 2048) (i : Fin 24) :
    generatedSeventhXiMiddleOddNumerator d i =
      generatedSeventhXiMiddleShortNumerator (Sum.inr (Sum.inr (d, i))) := by
  unfold generatedSeventhXiMiddleOddNumerator generatedSeventhXiMiddleShortNumerator
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro p _
  by_cases he : Sum.inr (Sum.inr (d, i)) = generatedSeventhXiShortOutputLabel s p
  · have hd := (generatedSeventhXiShortOutputLabel_odd_iff s p d i).mp he
    simp only [ite_eq_left he, ite_eq_left hd]
  · have hd := mt (generatedSeventhXiShortOutputLabel_odd_iff s p d i).mpr he
    simp only [ite_eq_right he, ite_eq_right hd]

/-- Each canonical middle odd row has this finite signed numerator divided by four. -/
theorem generatedSeventhXi_middle_odd_arithmetic (d : Fin 2048) (i : Fin 24) :
    (griessConwayEncode generatedSeventhXiPlaneCanonicalMiddle).2.1
      (Sum.inr (Sum.inr (d, i))) = (generatedSeventhXiMiddleOddNumerator d i : ℝ) / 4 := by
  rw [generatedSeventhXi_canonical_middle_short, generatedSeventhXiMiddleOddNumerator_eq]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
