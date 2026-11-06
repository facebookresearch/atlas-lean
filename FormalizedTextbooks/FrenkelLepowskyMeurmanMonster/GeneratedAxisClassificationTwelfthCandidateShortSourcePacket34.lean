/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthCandidateTrialityCachedSource
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthCompleteShortInputData

/-! A complete bounded original candidate short source packet. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 8000000 in
-- Check every original coordinate in this bounded complete source interval.
private theorem block_00 : ∀ u : Fin 256,
    if h : 34816 + u.val < 98280 then
      generatedTwelfthCandidateShortFormula (generatedNinthLowerSpinShortIndex ⟨34816 + u.val, h⟩) =
        (generatedTwelfthCompleteShortInputInteger
          (generatedNinthLowerSpinShortIndex ⟨34816 + u.val, h⟩) : ℚ) else True := by
  have hk : ∀ u : Fin 256,
    if h : 34816 + u.val < 98280 then
      generatedTwelfthCandidateShortTrialityCachedFormula (generatedNinthLowerSpinShortIndex ⟨34816 + u.val, h⟩) =
        (generatedTwelfthCompleteShortInputInteger
          (generatedNinthLowerSpinShortIndex ⟨34816 + u.val, h⟩) : ℚ) else True := by
    decide +kernel
  simpa only [← generatedTwelfth_candidate_short_triality_cached_actual] using hk

set_option maxHeartbeats 8000000 in
-- Check every original coordinate in this bounded complete source interval.
private theorem block_01 : ∀ u : Fin 256,
    if h : 35072 + u.val < 98280 then
      generatedTwelfthCandidateShortFormula (generatedNinthLowerSpinShortIndex ⟨35072 + u.val, h⟩) =
        (generatedTwelfthCompleteShortInputInteger
          (generatedNinthLowerSpinShortIndex ⟨35072 + u.val, h⟩) : ℚ) else True := by
  have hk : ∀ u : Fin 256,
    if h : 35072 + u.val < 98280 then
      generatedTwelfthCandidateShortTrialityCachedFormula (generatedNinthLowerSpinShortIndex ⟨35072 + u.val, h⟩) =
        (generatedTwelfthCompleteShortInputInteger
          (generatedNinthLowerSpinShortIndex ⟨35072 + u.val, h⟩) : ℚ) else True := by
    decide +kernel
  simpa only [← generatedTwelfth_candidate_short_triality_cached_actual] using hk

set_option maxHeartbeats 8000000 in
-- Check every original coordinate in this bounded complete source interval.
private theorem block_02 : ∀ u : Fin 256,
    if h : 35328 + u.val < 98280 then
      generatedTwelfthCandidateShortFormula (generatedNinthLowerSpinShortIndex ⟨35328 + u.val, h⟩) =
        (generatedTwelfthCompleteShortInputInteger
          (generatedNinthLowerSpinShortIndex ⟨35328 + u.val, h⟩) : ℚ) else True := by
  have hk : ∀ u : Fin 256,
    if h : 35328 + u.val < 98280 then
      generatedTwelfthCandidateShortTrialityCachedFormula (generatedNinthLowerSpinShortIndex ⟨35328 + u.val, h⟩) =
        (generatedTwelfthCompleteShortInputInteger
          (generatedNinthLowerSpinShortIndex ⟨35328 + u.val, h⟩) : ℚ) else True := by
    decide +kernel
  simpa only [← generatedTwelfth_candidate_short_triality_cached_actual] using hk

set_option maxHeartbeats 8000000 in
-- Check every original coordinate in this bounded complete source interval.
private theorem block_03 : ∀ u : Fin 256,
    if h : 35584 + u.val < 98280 then
      generatedTwelfthCandidateShortFormula (generatedNinthLowerSpinShortIndex ⟨35584 + u.val, h⟩) =
        (generatedTwelfthCompleteShortInputInteger
          (generatedNinthLowerSpinShortIndex ⟨35584 + u.val, h⟩) : ℚ) else True := by
  have hk : ∀ u : Fin 256,
    if h : 35584 + u.val < 98280 then
      generatedTwelfthCandidateShortTrialityCachedFormula (generatedNinthLowerSpinShortIndex ⟨35584 + u.val, h⟩) =
        (generatedTwelfthCompleteShortInputInteger
          (generatedNinthLowerSpinShortIndex ⟨35584 + u.val, h⟩) : ℚ) else True := by
    decide +kernel
  simpa only [← generatedTwelfth_candidate_short_triality_cached_actual] using hk

/-- Every original coordinate in this complete source packet has its exact rational numerator. -/
theorem generatedTwelfth_candidate_short_source_packet_34 (u : Fin 1024) :
    if h : 34816 + u.val < 98280 then
      generatedTwelfthCandidateShortFormula (generatedNinthLowerSpinShortIndex ⟨34816 + u.val, h⟩) =
        (generatedTwelfthCompleteShortInputInteger
          (generatedNinthLowerSpinShortIndex ⟨34816 + u.val, h⟩) : ℚ) else True := by
  have hp : ∀ (b : Fin 4) (v : Fin 256),
      if h : 34816 + b.val * 256 + v.val < 98280 then
        generatedTwelfthCandidateShortFormula
          (generatedNinthLowerSpinShortIndex ⟨34816 + b.val * 256 + v.val, h⟩) =
          (generatedTwelfthCompleteShortInputInteger
            (generatedNinthLowerSpinShortIndex ⟨34816 + b.val * 256 + v.val, h⟩) : ℚ) else True := by
    intro b v
    fin_cases b
    · exact block_00 v
    · exact block_01 v
    · exact block_02 v
    · exact block_03 v
  have h := hp ⟨u.val / 256, by omega⟩ ⟨u.val % 256, Nat.mod_lt _ (by decide)⟩
  have he : u.val / 256 * 256 + u.val % 256 = u.val := by omega
  simpa only [Nat.add_assoc, he] using h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
