/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthSparseOctad

/-! Literal phase and coefficient caches, certified against the actual full original Q image.
The values are arithmetic discovery from the repository's finite matrices and grey projections. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Literal central phase bits in the actual 63-octad ordering. -/
def generatedFourthEvenRootPhaseCache : Fin 63 → ZMod 2 :=
  ![0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1,
    1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0,
    0, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 16000000 in
-- Check all 63 genuine full preferred-Q images, including the exact central phases.
/-- Every cached phase is the actual original preferred-Q inverse phase. -/
theorem generatedFourth_even_phase_cache : ∀ j : Fin 63,
    generatedFourthEvenRootPhase j = generatedFourthEvenRootPhaseCache j := by
  unfold generatedFourthEvenRootPhase
  decide +kernel

/-- Literal complete middle octad coefficient phases, including original Fourier signs. -/
def generatedFourthEvenCoefficientCache : Fin 63 → ZMod 2 :=
  ![0, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1,
    0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1,
    0, 0, 1, 0, 1, 0, 1, 1, 0, 0, 1, 0, 1, 0, 1, 0,
    1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1]

/-- The finite cache includes the original input Fourier phase exactly. -/
theorem generatedFourth_even_coefficient_cache_certificate : ∀ j : Fin 63,
    generatedFourthEvenRootPhaseCache j + generatedFourthEvenRootInputPhase j =
      generatedFourthEvenCoefficientCache j := by
  decide +kernel

/-- The computable coefficient cache is the exact actual coefficient phase. -/
theorem generatedFourth_even_coefficient_cache (j : Fin 63) :
    generatedFourthEvenCoefficientPhase j = generatedFourthEvenCoefficientCache j := by
  unfold generatedFourthEvenCoefficientPhase
  rw [generatedFourth_even_phase_cache]
  exact generatedFourth_even_coefficient_cache_certificate j

/-- The actual sparse middle octad vector has the verified computable coefficient cache. -/
theorem generatedFourth_middle_octad_sparse_cache (o : Fin 759) (e : Fin 64) :
    localShortOperator generatedFourthLocalFiber
      (griessConwayEncode (sExtra (conwayShortAxis
        (Sum.inr (Sum.inl (generatedFourthOctad, 0))) 0))).2.1 (Sum.inr (Sum.inl (o, e))) =
      ∑ j : Fin 63, if generatedFourthEvenRootOutputLabel j = Sum.inr (Sum.inl (o, e)) then
        qSign (generatedFourthEvenCoefficientCache j) else 0 := by
  simpa only [generatedFourth_even_coefficient_cache] using generatedFourth_middle_octad_sparse o e

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
