/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthInputEightCoordinates

/-! Finite linearity gives an exact eight-state reduction of all original physical input columns. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The same eight-state reduction holds in the genuine real spin input space. -/
theorem generatedNinth_column_input_eight_embed (i : Fin 24) :
    nortonUIntegerEmbed (generatedNinthColumnInputInteger i) =
      ∑ b : Fin 8, (generatedNinthInputBasisCoefficients i b : ℝ) •
        nortonUIntegerEmbed (generatedNinthColumnInputInteger
          (generatedNinthInputBasisColumn b)) := by
  ext t
  change (generatedNinthColumnInputInteger i (nortonUIntegerLabel t) : ℝ) = _
  rw [generatedNinth_column_input_eight i (nortonUIntegerLabel t)]
  simp only [Int.cast_sum, Int.cast_mul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, nortonUIntegerEmbed]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
