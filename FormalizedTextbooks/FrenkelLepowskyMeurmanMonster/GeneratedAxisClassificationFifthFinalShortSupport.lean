/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthQFull
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMatrix

/-! Exact original nonzero octad rows of the actual final fifth axis. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The 56 actual middle octad families have distinct genuine Golay code labels. -/
theorem generatedFifth_even_codes_injective : Function.Injective generatedFifthEvenRootCode := by
  decide +kernel

/-- The 56 actual middle octad families have distinct catalogue indices. -/
theorem generatedFifth_even_octads_injective : Function.Injective generatedFifthEvenRootOctad := by
  intro j k h
  apply generatedFifth_even_codes_injective
  simpa only [generatedFifthEvenRootOctad_label] using congrArg golayOctadLabel h

/-- A genuine middle octad family contains only its one original signed row. -/
theorem generatedFifth_middle_octad_other_zero (j : Fin 56) (e : Fin 64)
    (he : e ≠ generatedFifthEvenRootSign j) :
    localShortOperator generatedFifthLocalFiber
      (griessConwayEncode (sExtra (conwayShortAxis
        (Sum.inr (Sum.inl (generatedFourthOctad, 0))) 0))).2.1
          (Sum.inr (Sum.inl (generatedFifthEvenRootOctad j, e))) = 0 := by
  apply not_ne_iff.mp
  intro hn
  rcases (generatedFifth_middle_nonzero_iff _).mp hn with ⟨k, hk⟩ | ⟨k, hk⟩
  · simp only [generatedFifthOddRootOutputLabel, Sum.inr.injEq, reduceCtorEq] at hk
  · have hp : (generatedFifthEvenRootOctad k, generatedFifthEvenRootSign k) =
        (generatedFifthEvenRootOctad j, e) := by
      simpa only [generatedFifthEvenRootOutputLabel, Sum.inr.injEq, Sum.inl.injEq] using hk
    have hkj := generatedFifth_even_octads_injective (congrArg Prod.fst hp)
    exact he ((congrArg Prod.snd hp).symm.trans (congrArg generatedFifthEvenRootSign hkj))

/-- All 64 outgoing signs of each genuine family retain its actual Fourier and preferred-Q phase. -/
theorem generatedFifth_final_octad_coordinate (j : Fin 56) (e : Fin 64) :
    (griessConwayEncode generatedFifthAxis).2.1
      (Sum.inr (Sum.inl (generatedFifthEvenRootOctad j, e))) =
        trialityRealMatrix e (generatedFifthEvenRootSign j) *
          qSign (generatedFifthEvenCoefficientPhase j) := by
  rw [generatedFifthAxis_local_expression, generatedFourthQShortBasis_triality_octad]
  rw [Finset.sum_eq_single (generatedFifthEvenRootSign j)]
  · rw [show (griessConwayEncode (rhoLocal (localFiberIntoH generatedFifthLocalFiber)
      (sExtra (conwayShortAxis (Sum.inr (Sum.inl (generatedFourthOctad, 0))) 0)))).2.1
        (Sum.inr (Sum.inl (generatedFifthEvenRootOctad j, generatedFifthEvenRootSign j))) =
        qSign (generatedFifthEvenCoefficientPhase j) from generatedFifth_even_middle_coefficient j]
  · intro f _ hf
    rw [generatedFourth_local_short, generatedFifth_middle_octad_other_zero j f hf, mul_zero]
  · simp only [Finset.mem_univ, not_true_eq_false, false_implies]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
