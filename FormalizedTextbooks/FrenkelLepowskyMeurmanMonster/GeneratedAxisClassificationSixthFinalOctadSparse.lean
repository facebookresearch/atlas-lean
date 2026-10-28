/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMiddleOctadCoefficients

/-! The complete genuine middle octad block is the sum of its 273 preferred signed rows. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Every actual middle octad coordinate is the complete displayed signed sparse sum. -/
theorem generatedSixth_middle_octad_sparse (o : Fin 759) (e : Fin 64) :
    (griessConwayEncode
      (rhoLocal (localFiberIntoH generatedSixthLocalFiber) generatedOddAxis)).2.1
        (Sum.inr (Sum.inl (o, e))) =
      ∑ j : Fin 273,
        if generatedSixthMiddleOctadOutput j = Sum.inr (Sum.inl (o, e)) then
          (generatedSixthMiddleOctadWeight j : ℝ) / 4 else 0 := by
  classical
  by_cases h : ∃ j : Fin 273,
      generatedSixthMiddleOctadOutput j = Sum.inr (Sum.inl (o, e))
  · obtain ⟨j, hj⟩ := h
    have he (k : Fin 273) :
        generatedSixthMiddleOctadOutput k = Sum.inr (Sum.inl (o, e)) ↔ k = j := by
      constructor
      · intro hk
        exact generatedSixthMiddleOctadOutput_injective (hk.trans hj.symm)
      · rintro rfl
        exact hj
    simp only [he, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [← hj, generatedSixth_middle_octad_coefficient]
  · rw [generatedSixth_middle_octad_zero o e h]
    symm
    apply Finset.sum_eq_zero
    intro j _
    have hj : generatedSixthMiddleOctadOutput j ≠ Sum.inr (Sum.inl (o, e)) :=
      fun hj => h ⟨j, hj⟩
    simp only [hj, ite_false]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
