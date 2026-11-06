/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPairPhaseData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPairImages

/-! All 552 local fifth-image pair coefficients retain their true source and preferred-Q phases. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- Every actual middle pair row has its exact signed original numerator divided by sixteen. -/
theorem generatedNinth_middle_pair_coefficient (r : Fin 552) :
    (griessConwayEncode (rhoLocal (localFiberIntoH generatedNinthLocalFiber)
      generatedFifthAxis)).2.1 (generatedNinthPairTargetIndex r) =
        (generatedNinthPairCoefficientNumerator r : ℝ) / 16 := by
  rw [generatedFourth_local_short, generatedNinth_pair_operator,
    generatedNinthInputShortNumerator_actual]
  have hc := generatedNinth_pair_coefficient_certificate r
  by_cases h : generatedNinthInputShortNumerator (generatedNinthPairSource r) = 0
  · rw [h, mul_zero] at hc
    simp only [h, Int.cast_zero, zero_div, mul_zero, ← hc]
  · obtain ⟨j, hj⟩ := generatedNinth_pair_supported_row r h
    have hp : localShortPhase generatedNinthLocalFiber
        (generatedNinthInputShortIndex (generatedNinthPairSource r)) =
          generatedNinthPairPhaseCache r := by
      rw [generatedNinth_input_short_phase]
      have hp := generatedNinth_pair_phase_certificate j
      simpa only [hj] using hp
    rw [hp]
    have he : (if generatedNinthPairPhaseCache r = 0 then (1 : ℝ) else -1) *
        (generatedNinthInputShortNumerator (generatedNinthPairSource r) : ℝ) =
          (generatedNinthPairCoefficientNumerator r : ℝ) := by
      exact_mod_cast hc
    change (if generatedNinthPairPhaseCache r = 0 then (1 : ℝ) else -1) *
      ((generatedNinthInputShortNumerator (generatedNinthPairSource r) : ℝ) / 16) = _
    rw [← mul_div_assoc, he]

/-- Every original preferred target pair is the certified lookup of its ordered coordinates. -/
theorem generatedNinth_pair_lookup_index (s : Fin 2) (p : Fin 276) :
    generatedNinthPairTargetIndex (generatedNinthPairLookup s
      (griessCoordinatePair p).1 (griessCoordinatePair p).2) = Sum.inl (s, p) := by
  have hl := (Finset.mem_filter.mp (griessCoordinatePairEquiv p).property).2
  change (griessCoordinatePair p).1 < (griessCoordinatePair p).2 at hl
  unfold generatedNinthPairTargetIndex
  simp only [generatedNinthPairLookup_target s _ _ hl, griessPairIndex_pair]

/-- Both preferred signs of every actual middle pair coordinate have the certified lookup value. -/
theorem generatedNinth_middle_pair (s : Fin 2) (p : Fin 276) :
    (griessConwayEncode (rhoLocal (localFiberIntoH generatedNinthLocalFiber)
      generatedFifthAxis)).2.1 (Sum.inl (s, p)) =
        (generatedNinthPairCoefficientNumerator (generatedNinthPairLookup s
          (griessCoordinatePair p).1 (griessCoordinatePair p).2) : ℝ) / 16 := by
  rw [← generatedNinth_pair_lookup_index s p]
  exact generatedNinth_middle_pair_coefficient _

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
