/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneShortPacketPackedOddSource

/-! The original outgoing odd coefficients have their complete finite signed basis expansion. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Every original low-code scalar is exactly the sum over its checked occurring family. -/
theorem generatedSeventhXiShortOddScalar_sum (d : Fin 2048) :
    generatedSeventhXiShortOddScalar d =
      ∑ g : Fin 512, (if generatedSeventhXiShortPackedOddCode g = d then
        (if generatedSeventhXiShortPackedOddSignBits.testBit g.val then (-1 : ℤ) else 1)
        else 0) := by
  have hs := generatedSeventhXiShortPackedOdd_support d
  by_cases hi : generatedSeventhXiShortPackedOddInverse d < 512
  · rw [dite_eq_left hi] at hs
    let g : Fin 512 := ⟨generatedSeventhXiShortPackedOddInverse d, hi⟩
    change generatedSeventhXiShortPackedOddCode g = d ∧ _ at hs
    rw [Finset.sum_eq_single g]
    · rw [ite_eq_left hs.1]
      exact hs.2
    · intro h _ hh
      have he : generatedSeventhXiShortPackedOddCode h ≠ d := by
        intro hd
        have heq := generatedSeventhXiShortPackedOddCode_injective (hd.trans hs.1.symm)
        exact hh heq
      exact ite_eq_right he
    · simp
  · rw [dite_eq_right hi] at hs
    rw [hs]
    symm
    apply Finset.sum_eq_zero
    intro g _
    have he : generatedSeventhXiShortPackedOddCode g ≠ d := by
      intro hd
      have heq := generatedSeventhXiShortPackedOdd_inverse g
      rw [hd] at heq
      exact hi (heq ▸ g.isLt)
    exact ite_eq_right he

/-- The complete canonical odd row retains every original signed numerator, including zero rows. -/
theorem generatedSeventhXiShortOddCoefficient_sum (d : Fin 2048) (j : Fin 24) :
    (griessConwayEncode generatedSeventhXiPlaneCanonicalAxis).2.1
      (Sum.inr (Sum.inr (d, j))) =
        ∑ g : Fin 512,
          if generatedSeventhXiShortPackedOddCode g = d then
            (generatedSeventhXiShortPackedOddCoefficient g j : ℝ) / 32 else 0 := by
  rw [generatedSeventhXiShortOddScalar_actual, generatedSeventhXiShortOddScalar_sum]
  simp only [Int.cast_sum, Finset.sum_mul, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro g _
  by_cases h : generatedSeventhXiShortPackedOddCode g = d
  · rw [ite_eq_left h, ite_eq_left h]
    simp only [generatedSeventhXiShortPackedOddCoefficient, Int.cast_mul]
  · simp only [ite_eq_right h, Int.cast_zero, zero_mul, zero_div]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
