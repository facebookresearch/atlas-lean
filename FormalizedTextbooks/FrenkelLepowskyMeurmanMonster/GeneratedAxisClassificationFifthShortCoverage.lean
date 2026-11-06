/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthInputEnumeration
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthOddCoefficients
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthEvenCoefficients

/-! Exact support of all 120 genuine middle short coordinates of the fifth prototype. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Every nonzero middle short row is one of the checked 64 odd or 56 octad outputs. -/
theorem generatedFifth_middle_nonzero_iff (r : GriessShortIndex) :
    localShortOperator generatedFifthLocalFiber
      (griessConwayEncode (sExtra (conwayShortAxis
        (Sum.inr (Sum.inl (generatedFourthOctad, 0))) 0))).2.1 r ≠ 0 ↔
      (∃ j : Fin 64, generatedFifthOddRootOutputLabel j = r) ∨
        (∃ j : Fin 56, generatedFifthEvenRootOutputLabel j = r) := by
  let s := griessShortPermutation (generatedFifthLocalFiber⁻¹).val.2 r
  have hperm := griessShortPermutation_vector (generatedFifthLocalFiber⁻¹).val.2 r
  constructor
  · intro hn
    have hsphys := (generatedFourth_transported_short_support generatedFifthLocalFiber
      generatedFourthOctad 0 0 r).mp hn
    have hsup : generatedOctadShortSupport generatedFourthOctad s := by
      apply (generatedOctadShortSupport_iff_physical generatedFourthOctad s).mpr
      rcases hperm with hp | hp
      · simpa only [hp] using hsphys
      · simpa only [hp, Pi.neg_apply, neg_eq_zero] using hsphys
    rcases generatedFifth_supported_input_enumeration s hsup with ⟨j, hj⟩ | ⟨j, hj⟩
    · left
      refine ⟨j, (griessShortPermutation (generatedFifthLocalFiber⁻¹).val.2).injective ?_⟩
      exact (generatedFifth_odd_inverse_permutation j).trans hj
    · right
      refine ⟨j, (griessShortPermutation (generatedFifthLocalFiber⁻¹).val.2).injective ?_⟩
      exact (generatedFifth_even_inverse_permutation j).trans hj
  · rintro (⟨j, rfl⟩ | ⟨j, rfl⟩)
    · have hc := generatedFifth_odd_middle_coefficient j
      rw [generatedFourth_local_short] at hc
      rw [hc]
      intro hz
      have hu := qSign_sq (generatedFifthOddCoefficientPhaseData j)
      rw [hz] at hu
      norm_num at hu
    · have hc := generatedFifth_even_middle_coefficient j
      rw [generatedFourth_local_short] at hc
      rw [hc]
      intro hz
      have hu := qSign_sq (generatedFifthEvenCoefficientPhase j)
      rw [hz] at hu
      norm_num at hu

/-- The exact odd middle support is the 64 genuine checked dictionary entries. -/
theorem generatedFifth_odd_middle_nonzero_iff (d : Fin 2048) (i : Fin 24) :
    localShortOperator generatedFifthLocalFiber
      (griessConwayEncode (sExtra (conwayShortAxis
        (Sum.inr (Sum.inl (generatedFourthOctad, 0))) 0))).2.1
        (Sum.inr (Sum.inr (d, i))) ≠ 0 ↔
      ∃ j : Fin 64, generatedFifthOddRootOutputData j = (d, i) := by
  rw [generatedFifth_middle_nonzero_iff]
  simp only [generatedFifthOddRootOutputLabel, generatedFifthEvenRootOutputLabel,
    Sum.inr.injEq, reduceCtorEq, exists_false, or_false]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
