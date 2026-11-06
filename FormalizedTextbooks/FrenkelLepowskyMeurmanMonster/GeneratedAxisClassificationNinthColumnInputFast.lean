/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthColumnInputSparse

/-! A source-proved branch order skips coefficients with a zero original address indicator. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The same 64 original signed source terms, with the address indicator evaluated first. -/
def generatedNinthColumnInputFast (i : Fin 24) (n : Fin 4096) : ℤ :=
  ∑ k : Fin 64,
    if n.val % 2048 = (generatedFifthOddRootOutputData k).1.val then
      nortonUIntegerSign (generatedFifthOddCoefficientPhaseData k) *
        nortonUIntegerSign ((golayLabelCoefficients n) 11) *
        (if (golayEncodedMask (generatedFifthOddRootOutputData k).1.val).testBit
          (generatedFifthOddRootOutputData k).2.val then -1 else 1) *
        generatedNinthFrameVectorData 9 (generatedFifthOddRootOutputData k).2 i
    else 0

/-- Moving the genuine zero address indicator to the front preserves every original term. -/
theorem generatedNinth_column_input_sparse_fast (i : Fin 24) (n : Fin 4096) :
    generatedNinthColumnInputSparse i n = generatedNinthColumnInputFast i n := by
  unfold generatedNinthColumnInputSparse generatedNinthColumnInputFast
  apply Finset.sum_congr rfl
  intro k _
  by_cases h : n.val % 2048 = (generatedFifthOddRootOutputData k).1.val
  · simp only [h, ite_true, mul_one]
  · simp only [h, ite_false, mul_zero, zero_mul]

/-- The executable branch ordering is the literal original integer source input. -/
theorem generatedNinth_column_input_fast (i : Fin 24) (n : Fin 4096) :
    generatedNinthColumnInputInteger i n = generatedNinthColumnInputFast i n := by
  rw [generatedNinth_column_input_sparse, generatedNinth_column_input_sparse_fast]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
