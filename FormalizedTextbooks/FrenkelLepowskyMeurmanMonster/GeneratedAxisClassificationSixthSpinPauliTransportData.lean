/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthSpinPauliData

/-! All twelve full Pauli transports are original-generator coordinate certificates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
open scoped Matrix

set_option maxHeartbeats 4000000 in
-- Check 96 full original Pauli transitions, including all binary and central coordinates.
/-- Each full cached successor is the original Pauli action with its central phase. -/
theorem generatedSixth_spin_pauli_cache_certificate : ∀ j : Fin 12,
    generatedSixthSpinPauliCache j 1 =
      generatedSixthQGenerator 0 (generatedSixthSpinPauliCache j 0) ∧
    generatedSixthSpinPauliCache j 2 =
      generatedSixthQGenerator 2 (generatedSixthSpinPauliCache j 1) ∧
    generatedSixthSpinPauliCache j 3 =
      generatedSixthQGenerator 0 (generatedSixthSpinPauliCache j 2) ∧
    generatedSixthSpinPauliCache j 4 =
      generatedSixthQGenerator 1 (generatedSixthSpinPauliCache j 3) ∧
    generatedSixthSpinPauliCache j 5 =
      generatedSixthQGenerator 0 (generatedSixthSpinPauliCache j 4) ∧
    generatedSixthSpinPauliCache j 6 =
      generatedSixthQGenerator 2 (generatedSixthSpinPauliCache j 5) ∧
    generatedSixthSpinPauliCache j 7 =
      generatedSixthQGenerator 1 (generatedSixthSpinPauliCache j 6) ∧
    generatedSixthSpinPauliCache j 8 =
      generatedSixthQGenerator 2 (generatedSixthSpinPauliCache j 7) := by
  intro j
  fin_cases j <;> refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals apply NormalizedCocycleExtension.Extension.ext
  all_goals decide +kernel

set_option maxHeartbeats 2000000 in
-- Verify all 108 selected final translation coordinates against the full original Q cache.
/-- The rank-nine matrix columns are the actual final Pauli translations. -/
theorem generatedSixth_spin_pauli_translation_coordinate : ∀ j : Fin 9, ∀ i : Fin 12,
    spinTranslation (generatedSixthSpinPauliCache (generatedSixthSpinPauliIndependent j) 8) i =
      generatedSixthSpinPauliTranslationMatrix i j := by
  decide +kernel

/-- A product of two actual final Pauli generators is the genuine odd-parity pure modulation. -/
theorem generatedSixth_spin_pauli_odd_modulation :
    generatedSixthSpinPauliCache 4 8 * generatedSixthSpinPauliCache 5 8 =
      cocodeQ (golayLabelCoefficients 3079) := by
  apply NormalizedCocycleExtension.Extension.ext <;> decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
