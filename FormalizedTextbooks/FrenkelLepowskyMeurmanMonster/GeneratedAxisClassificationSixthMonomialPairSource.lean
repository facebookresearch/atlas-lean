/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialPairData

/-! Genuine source pair indices and the original cleared numerator on their sorted coordinates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- Each frozen original spatial input array is a permutation of the actual coordinates. -/
theorem generatedSixth_monomial_pair_input_injective : ∀ k : Fin 4,
    Function.Injective (generatedSixthMonomialPairInput k) := by
  decide +kernel

/-- The genuine source pair of an actual target pair under the original monomial. -/
def generatedSixthMonomialPairSourceIndex (k : Fin 4) (p : Fin 276) : Fin 276 :=
  let a := generatedSixthMonomialPairInput k (griessCoordinatePair p).1
  let b := generatedSixthMonomialPairInput k (griessCoordinatePair p).2
  have hn : a ≠ b := fun h => griessCoordinatePair_ne p
    (generatedSixth_monomial_pair_input_injective k h)
  griessPairIndex a b hn

/-- Original unordered source coordinates are sorted by the genuine pair-index equivalence. -/
theorem generatedSixth_monomial_pair_source_coordinates (k : Fin 4) (p : Fin 276) :
    griessCoordinatePair (generatedSixthMonomialPairSourceIndex k p) =
      let a := generatedSixthMonomialPairInput k (griessCoordinatePair p).1
      let b := generatedSixthMonomialPairInput k (griessCoordinatePair p).2
      if a < b then (a, b) else (b, a) := by
  unfold generatedSixthMonomialPairSourceIndex
  exact griessPairIndex_coordinates _ _ _

/-- The executable target numerator equals the full actual preferred-pair numerator. -/
theorem generatedSixth_monomial_pair_target_numerator (s : Fin 2) (p : Fin 276) :
    generatedSixthMonomialPairNumerator s (griessCoordinatePair p).1
      (griessCoordinatePair p).2 = generatedSixthFinalPairNumerator s p := by
  have hp : (griessCoordinatePair p).1 < (griessCoordinatePair p).2 :=
    (Finset.mem_filter.mp (griessCoordinatePairEquiv p).property).2
  simp only [generatedSixthMonomialPairNumerator, min_eq_left (le_of_lt hp),
    max_eq_right (le_of_lt hp), generatedSixthFinalPairNumerator]

/-- The executable inverse-coordinate numerator equals the full genuine source-pair numerator. -/
theorem generatedSixth_monomial_pair_source_numerator (k : Fin 4) (s : Fin 2) (p : Fin 276) :
    generatedSixthMonomialPairNumerator s
      (generatedSixthMonomialPairInput k (griessCoordinatePair p).1)
      (generatedSixthMonomialPairInput k (griessCoordinatePair p).2) =
        generatedSixthFinalPairNumerator s (generatedSixthMonomialPairSourceIndex k p) := by
  unfold generatedSixthFinalPairNumerator
  rw [generatedSixth_monomial_pair_source_coordinates]
  dsimp only
  by_cases h : generatedSixthMonomialPairInput k (griessCoordinatePair p).1 <
      generatedSixthMonomialPairInput k (griessCoordinatePair p).2
  · simp [h, generatedSixthMonomialPairNumerator, min_eq_left (le_of_lt h),
      max_eq_right (le_of_lt h)]
  · simp [h, generatedSixthMonomialPairNumerator, min_eq_right (le_of_not_gt h),
      max_eq_left (le_of_not_gt h)]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
