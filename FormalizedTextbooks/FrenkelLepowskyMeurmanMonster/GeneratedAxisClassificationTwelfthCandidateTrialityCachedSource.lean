/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthTrialityIntegerCache
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthCandidateOctadCachedSourceFormula

/-! Cached original Fourier signs evaluate the complete unchanged source formula. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

/-- Every complete original source coefficient uses the checked original Fourier sign cache. -/
def generatedTwelfthCandidateShortTrialityCachedFormula : GriessShortIndex → ℚ
  | Sum.inr (Sum.inl (o, e)) =>
      ((∑ f : Fin 64, generatedTwelfthTrialityIntegerCache e f *
        generatedTwelfthIncomingOctadCache o f) : ℤ)
  | r => generatedTwelfthCandidateShortOctadCachedFormula r

/-- All original coefficients retain their exact signs and rational normalization. -/
theorem generatedTwelfth_candidate_short_triality_cached_actual (r : GriessShortIndex) :
    generatedTwelfthCandidateShortFormula r =
      generatedTwelfthCandidateShortTrialityCachedFormula r := by
  rw [generatedTwelfth_candidate_short_octad_cached_actual]
  rcases r with p | (⟨o, e⟩ | ⟨d, i⟩)
  · rfl
  · simp only [generatedTwelfthCandidateShortTrialityCachedFormula,
      generatedTwelfthCandidateShortOctadCachedFormula,
      generatedTwelfth_triality_integer_cache_actual]
  · rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
