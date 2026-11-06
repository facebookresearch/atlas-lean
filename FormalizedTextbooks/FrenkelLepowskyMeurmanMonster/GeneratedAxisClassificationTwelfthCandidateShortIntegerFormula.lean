/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthCandidateShortKernelFormula

/-! Exact integer arithmetic evaluates the complete octad and odd source sums before their
single rational cast. The physical pair formula is retained. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

/-- Complete source sums use their exact integer arithmetic wherever every term is integral. -/
def generatedTwelfthCandidateShortIntegerFormula : GriessShortIndex → ℚ
  | Sum.inl p => generatedTwelfthCandidateShortKernelFormula (Sum.inl p)
  | Sum.inr (Sum.inl (o, e)) =>
      ((∑ f : Fin 64, trialityIntegerMatrix e f *
        generatedTwelfthIncomingShortCoefficient (Sum.inr (Sum.inl (o, f)))) : ℤ)
  | Sum.inr (Sum.inr (d, i)) =>
      (nortonUIntegerSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) *
        (generatedTwelfthIncomingSpinTensorOutputInteger ⟨d.val, by omega⟩ i +
          generatedTwelfthIncomingSpinTensorOutputInteger ⟨d.val + 2048, by omega⟩ i) : ℤ)

/-- Every original source coefficient equals the exact integer evaluation with one cast. -/
theorem generatedTwelfth_candidate_short_integer_kernel (r : GriessShortIndex) :
    generatedTwelfthCandidateShortKernelFormula r =
      generatedTwelfthCandidateShortIntegerFormula r := by
  rcases r with p | (⟨o, e⟩ | ⟨d, i⟩)
  · rfl
  · simp only [generatedTwelfthCandidateShortIntegerFormula,
      generatedTwelfthCandidateShortKernelFormula, Int.cast_sum, Int.cast_mul]
  · simp only [generatedTwelfthCandidateShortIntegerFormula,
      generatedTwelfthCandidateShortKernelFormula, Int.cast_mul, Int.cast_add]

/-- The complete original rational formula is preserved by the integer source evaluator. -/
theorem generatedTwelfth_candidate_short_integer_actual (r : GriessShortIndex) :
    generatedTwelfthCandidateShortFormula r =
      generatedTwelfthCandidateShortIntegerFormula r := by
  rw [generatedTwelfth_candidate_short_kernel_formula_actual,
    generatedTwelfth_candidate_short_integer_kernel]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
