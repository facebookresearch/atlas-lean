/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthIncomingShortData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthIncomingSpinTensorInputData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthMatrixCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.NortonUIntegerSpinBasic
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.TrialityOrder
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthCandidateShortFormulaData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsPairCoordinates

/-! A computable physical pair catalogue retains the complete original rational triality source formula. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option maxRecDepth 100000

open scoped BigOperators

/-- The entire normalized candidate short constituent from the original incoming blocks. -/
def generatedTwelfthCandidateShortKernelFormula : GriessShortIndex → ℚ
  | Sum.inl (s, p) =>
      (if s = 0 then 128 else -128) *
        generatedTwelfthIncomingMatrixQ (generatedAxisGlobalPairCoordinates p).1 (generatedAxisGlobalPairCoordinates p).2 +
      4 * ((generatedTwelfthIncomingShortCoefficient (Sum.inl (0, p)) : ℚ) -
        (generatedTwelfthIncomingShortCoefficient (Sum.inl (1, p)) : ℚ))
  | Sum.inr (Sum.inl (o, e)) =>
      ∑ f : Fin 64, (trialityIntegerMatrix e f : ℚ) *
        (generatedTwelfthIncomingShortCoefficient (Sum.inr (Sum.inl (o, f))) : ℚ)
  | Sum.inr (Sum.inr (d, i)) =>
      (nortonUIntegerSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) : ℚ) *
        ((generatedTwelfthIncomingSpinTensorOutputInteger ⟨d.val, by omega⟩ i : ℚ) +
          (generatedTwelfthIncomingSpinTensorOutputInteger ⟨d.val + 2048, by omega⟩ i : ℚ))

/-- Replacing the finite chooser by its checked physical catalogue preserves every source coefficient. -/
theorem generatedTwelfth_candidate_short_kernel_formula_actual (r : GriessShortIndex) :
    generatedTwelfthCandidateShortFormula r = generatedTwelfthCandidateShortKernelFormula r := by
  rcases r with ⟨s, p⟩ | (⟨o, e⟩ | ⟨d, i⟩)
  · simp only [generatedTwelfthCandidateShortFormula, generatedTwelfthCandidateShortKernelFormula,
      ← generatedAxisGlobalPairCoordinates_actual]
  · rfl
  · rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
