/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSeventhSpinPauliData

/-! All twelve full Pauli transports are original-generator coordinate certificates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
open scoped Matrix

set_option maxHeartbeats 4000000 in
-- Check 84 full original Pauli transitions, including all binary and central coordinates.
/-- Each full cached successor is the original Pauli action with its central phase. -/
theorem generatedSeventh_spin_pauli_cache_certificate : ∀ j : Fin 12,
    generatedSeventhSpinPauliCache j 1 =
      generatedSeventhQGenerator 2 (generatedSeventhSpinPauliCache j 0) ∧
    generatedSeventhSpinPauliCache j 2 =
      generatedSeventhQGenerator 0 (generatedSeventhSpinPauliCache j 1) ∧
    generatedSeventhSpinPauliCache j 3 =
      generatedSeventhQGenerator 1 (generatedSeventhSpinPauliCache j 2) ∧
    generatedSeventhSpinPauliCache j 4 =
      generatedSeventhQGenerator 0 (generatedSeventhSpinPauliCache j 3) ∧
    generatedSeventhSpinPauliCache j 5 =
      generatedSeventhQGenerator 2 (generatedSeventhSpinPauliCache j 4) ∧
    generatedSeventhSpinPauliCache j 6 =
      generatedSeventhQGenerator 1 (generatedSeventhSpinPauliCache j 5) ∧
    generatedSeventhSpinPauliCache j 7 =
      generatedSeventhQGenerator 2 (generatedSeventhSpinPauliCache j 6) := by
  intro j
  fin_cases j <;> refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals apply NormalizedCocycleExtension.Extension.ext
  all_goals decide +kernel

set_option maxHeartbeats 2000000 in
-- Verify all 108 selected final translation coordinates against the full original Q cache.
/-- The rank-nine matrix columns are the actual final Pauli translations. -/
theorem generatedSeventh_spin_pauli_translation_coordinate : ∀ j : Fin 9, ∀ i : Fin 12,
    spinTranslation (generatedSeventhSpinPauliCache (generatedSeventhSpinPauliIndependent j) 7) i =
      generatedSeventhSpinPauliTranslationMatrix i j := by
  decide +kernel

/-- A product of two actual final Pauli generators is the genuine odd-parity pure modulation. -/
theorem generatedSeventh_spin_pauli_odd_modulation :
    generatedSeventhSpinPauliCache 5 7 * generatedSeventhSpinPauliCache 10 7 =
      cocodeQ (golayLabelCoefficients 3079) := by
  apply NormalizedCocycleExtension.Extension.ext <;> decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
