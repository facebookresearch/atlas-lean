/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationEighthQPauliData

/-! Kernel certificates for every original Pauli successor, final coordinate and left inverse. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 4000000 in
-- Verify all eighty-four full original successors, retaining binary and central coordinates.
/-- Every cached successor is the genuine primitive preferred-Q action. -/
theorem generatedEighth_spin_pauli_cache_certificate : ∀ j : Fin 12,
    generatedEighthSpinPauliCache j 1 =
      generatedEighthQGenerator 2 (generatedEighthSpinPauliCache j 0) ∧
    generatedEighthSpinPauliCache j 2 =
      generatedEighthQGenerator 0 (generatedEighthSpinPauliCache j 1) ∧
    generatedEighthSpinPauliCache j 3 =
      generatedEighthQGenerator 1 (generatedEighthSpinPauliCache j 2) ∧
    generatedEighthSpinPauliCache j 4 =
      generatedEighthQGenerator 2 (generatedEighthSpinPauliCache j 3) ∧
    generatedEighthSpinPauliCache j 5 =
      generatedEighthQGenerator 0 (generatedEighthSpinPauliCache j 4) ∧
    generatedEighthSpinPauliCache j 6 =
      generatedEighthQGenerator 1 (generatedEighthSpinPauliCache j 5) ∧
    generatedEighthSpinPauliCache j 7 =
      generatedEighthQGenerator 2 (generatedEighthSpinPauliCache j 6) := by
  intro j
  fin_cases j <;> refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals apply NormalizedCocycleExtension.Extension.ext
  all_goals decide +kernel

set_option maxHeartbeats 2000000 in
-- Check all twelve original initial Pauli elements, including their central coefficients.
/-- The cached initial operators are the genuine fixers of the original Hadamard state. -/
theorem generatedEighth_spin_pauli_initial : ∀ j : Fin 12,
    generatedEighthSpinPauliCache j 0 = generatedSixthSpinPauliInitial j := by
  intro j
  fin_cases j <;> apply NormalizedCocycleExtension.Extension.ext <;> decide +kernel

set_option maxHeartbeats 2000000 in
-- Check every one of the 132 selected original translation coordinates.
/-- The eleven matrix columns are genuine final translations. -/
theorem generatedEighth_spin_pauli_translation_coordinate : ∀ j : Fin 11, ∀ i : Fin 12,
    spinTranslation (generatedEighthSpinPauliCache (generatedEighthSpinPauliIndependent j) 7) i =
      generatedEighthSpinPauliTranslationMatrix i j := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Check all 121 binary product entries in the twelve-dimensional original module.
/-- The actual eleven translation columns are independent. -/
theorem generatedEighth_spin_pauli_left_inverse :
    generatedEighthSpinPauliLeftInverse * generatedEighthSpinPauliTranslationMatrix = 1 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Check the complete central coefficient of this product of five genuine final generators.
/-- A genuine fixing product is the odd-parity pure modulation. -/
theorem generatedEighth_spin_pauli_odd_modulation :
    generatedEighthSpinPauliCache 0 7 * generatedEighthSpinPauliCache 2 7 *
      generatedEighthSpinPauliCache 3 7 * generatedEighthSpinPauliCache 10 7 *
      generatedEighthSpinPauliCache 11 7 = cocodeQ (golayLabelCoefficients 3079) := by
  apply NormalizedCocycleExtension.Extension.ext <;> decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
