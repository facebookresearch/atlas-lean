/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightIncomingMatrixCache
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialSignFourierCache

/-! Exact finite short-source evaluation with the original matrix and Fourier entries. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- All original short-source families, using previously checked exact entry lookups. -/
def generatedRootEightPositiveFinalShortFastNumerator : GriessShortIndex → ℤ
  | Sum.inl (s, p) =>
      8 * (generatedFifthRootEightShortCachedCoefficient (Sum.inl (0, p)) -
        generatedFifthRootEightShortCachedCoefficient (Sum.inl (1, p))) +
      (if s = 0 then 1 else -1) * generatedRootEightIncomingMatrixCachedNumerator
        (griessCoordinatePair p).1 (griessCoordinatePair p).2
  | Sum.inr (Sum.inl (o, e)) =>
      2 * ∑ f : Fin 64, generatedFifthSignFourierCache e f *
        generatedFifthRootEightShortCachedCoefficient (Sum.inr (Sum.inl (o, f)))
  | Sum.inr (Sum.inr (d, i)) =>
      2 * (if ((golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) : ZMod 2) = 0 then 1 else -1) *
        (generatedRootEightIncomingPositiveTensorNumerator ⟨d.val, by omega⟩ i +
          generatedRootEightIncomingPositiveTensorNumerator ⟨d.val + 2048, by omega⟩ i)

/-- Every original numerator is unchanged, including the complete sums and zero coordinates. -/
theorem generatedRootEight_positive_final_short_fast_actual (r : GriessShortIndex) :
    generatedRootEightPositiveFinalShortFastNumerator r =
      generatedRootEightPositiveFinalShortNumerator r := by
  rcases r with ⟨s, p⟩ | (⟨o, e⟩ | ⟨d, i⟩)
  · simp only [generatedRootEightPositiveFinalShortFastNumerator,
      generatedRootEightPositiveFinalShortNumerator,
      ← generatedRootEight_incoming_matrix_numerator_cache]
  · simp only [generatedRootEightPositiveFinalShortFastNumerator,
      generatedRootEightPositiveFinalShortNumerator, generatedFifth_sign_fourier_cache]
  · rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
