/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthGolayMaskCacheActual
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthCandidateShortIntegerFormula
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthIncomingCandidateFinalTensorData

/-! Exact cached original codewords and weight signs evaluate complete candidate source
formulas while preserving every original coordinate and rational normalization. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The complete original short formula with the exact cached odd weight sign. -/
def generatedTwelfthCandidateShortCachedFormula : GriessShortIndex → ℚ
  | Sum.inr (Sum.inr (d, i)) =>
      (generatedTwelfthGolayPhaseCache d *
        (generatedTwelfthIncomingSpinTensorOutputInteger ⟨d.val, by omega⟩ i +
          generatedTwelfthIncomingSpinTensorOutputInteger ⟨d.val + 2048, by omega⟩ i) : ℤ)
  | r => generatedTwelfthCandidateShortIntegerFormula r

/-- Every original rational short coefficient is preserved by the cached source formula. -/
theorem generatedTwelfth_candidate_short_cached_actual (r : GriessShortIndex) :
    generatedTwelfthCandidateShortFormula r = generatedTwelfthCandidateShortCachedFormula r := by
  rw [generatedTwelfth_candidate_short_integer_actual]
  rcases r with p | (⟨o, e⟩ | ⟨d, i⟩)
  · rfl
  · rfl
  · simp only [generatedTwelfthCandidateShortCachedFormula,
      generatedTwelfthCandidateShortIntegerFormula, generatedTwelfth_golay_phase_cache_actual]

/-- The complete original outgoing tensor formula uses the exact cached codeword and sign. -/
def generatedTwelfthCandidateFinalTensorCachedInteger (n : Fin 4096) (i : Fin 24) : ℤ :=
  let d : Fin 2048 := ⟨n.val % 2048, Nat.mod_lt _ (by decide)⟩
  let sigma : ℤ := if (generatedTwelfthGolayMaskCache d).testBit i.val then -1 else 1
  (if n.val < 2048 then 8 else -8) * sigma * generatedTwelfthCandidateIncomingOddCoefficient d i +
    sigma * generatedTwelfthGolayPhaseCache d *
      (generatedTwelfthCandidateIncomingTensorNumerator ⟨d.val, by omega⟩ i -
        generatedTwelfthCandidateIncomingTensorNumerator ⟨d.val + 2048, by omega⟩ i)

/-- Every outgoing tensor coordinate retains its full original exact source numerator. -/
theorem generatedTwelfth_candidate_final_tensor_cached_actual (n : Fin 4096) (i : Fin 24) :
    generatedTwelfthCandidateFinalTensorCachedInteger n i =
      generatedTwelfthCandidateFinalTensorInteger n i := by
  simp only [generatedTwelfthCandidateFinalTensorCachedInteger,
    generatedTwelfthCandidateFinalTensorInteger, generatedTwelfth_golay_mask_cache_actual,
    generatedTwelfth_golay_phase_cache_actual]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
