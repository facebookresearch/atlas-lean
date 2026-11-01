/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthInputEight

/-! The genuine complete middle tensor reduces to eight actual source spin columns. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- All twenty-four actual middle tensor columns are determined by the eight selected columns. -/
theorem generatedNinth_middle_tensor_eight (t : SpinIndex) (i : Fin 24) :
    (griessConwayEncode (rhoLocal (localFiberIntoH generatedNinthLocalFiber)
      generatedFifthAxis)).2.2 t i =
        ∑ b : Fin 8, (generatedNinthInputBasisCoefficients i b : ℝ) *
          (griessConwayEncode (rhoLocal (localFiberIntoH generatedNinthLocalFiber)
            generatedFifthAxis)).2.2 t (generatedNinthInputBasisColumn b) := by
  rw [generatedNinth_middle_column_integer,
    generatedNinth_column_integer_eight i (nortonUIntegerLabel t)]
  simp only [Int.cast_sum, Int.cast_mul]
  simp_rw [generatedNinth_middle_column_integer]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro b _
  ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
