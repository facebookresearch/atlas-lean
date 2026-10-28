/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthIncomingOctadCacheActual
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthCandidateCachedSourceFormulas

/-! One-time exact octad caches evaluate the unchanged complete original source formula. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

/-- The complete original candidate source formula uses the exact incoming octad row cache. -/
def generatedTwelfthCandidateShortOctadCachedFormula : GriessShortIndex → ℚ
  | Sum.inr (Sum.inl (o, e)) =>
      ((∑ f : Fin 64, trialityIntegerMatrix e f *
        generatedTwelfthIncomingOctadCache o f) : ℤ)
  | r => generatedTwelfthCandidateShortCachedFormula r

/-- Every original source coefficient retains its exact sign and rational normalization. -/
theorem generatedTwelfth_candidate_short_octad_cached_actual (r : GriessShortIndex) :
    generatedTwelfthCandidateShortFormula r = generatedTwelfthCandidateShortOctadCachedFormula r := by
  rw [generatedTwelfth_candidate_short_cached_actual]
  rcases r with p | (⟨o, e⟩ | ⟨d, i⟩)
  · rfl
  · simp only [generatedTwelfthCandidateShortOctadCachedFormula,
      generatedTwelfthCandidateShortCachedFormula, generatedTwelfthCandidateShortIntegerFormula,
      generatedTwelfth_incoming_octad_cache_actual]
  · rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
