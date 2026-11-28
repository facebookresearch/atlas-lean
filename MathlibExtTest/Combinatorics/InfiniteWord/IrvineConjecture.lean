/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.InfiniteWord.IrvineConjecture

open MetaMathlibExt

-- The API includes the empty prefix, with no shift in the index of the sequence.
example : gutkovskiy 0 = ∑ i ∈ Finset.range 0, (kimberlingWord i).toNat :=
  gutkovskiy_eq_sum_kimberlingWord 0

-- The first block ends in a zero; the next letter starts a new block.
example : kimberlingWord 2 = false ∧ kimberlingWord 3 = true := by decide

example : (∑ i ∈ Finset.range 3, (kimberlingWord i).toNat) = 2 ∧
    (∑ i ∈ Finset.range 4, (kimberlingWord i).toNat) = 3 := by
  rw [← gutkovskiy_eq_sum_kimberlingWord 3, ← gutkovskiy_eq_sum_kimberlingWord 4]
  decide

-- Index 8 is the first letter outside the second Kimberling block.
example : kimberlingWord 8 = true := by decide

example : (∑ i ∈ Finset.range 8, (kimberlingWord i).toNat) = 6 ∧
    (∑ i ∈ Finset.range 9, (kimberlingWord i).toNat) = 7 := by
  rw [← gutkovskiy_eq_sum_kimberlingWord 8, ← gutkovskiy_eq_sum_kimberlingWord 9]
  decide

-- Count directly in the word: A₁ = 1, B₁ = 3, and A₃ = 4, giving exact equality.
example : kimberlingOnePosition (kimberlingZeroPosition 1) =
    kimberlingOnePosition 1 + kimberlingZeroPosition 1 := by
  have hA : kimberlingOnePosition 1 = 1 :=
    kimberlingOnePosition_eq_succ_of_count (n := 0) (i := 0) (by decide) (by decide)
  have hB : kimberlingZeroPosition 1 = 3 :=
    kimberlingZeroPosition_eq_succ_of_count (n := 0) (i := 2) (by decide) (by decide)
  have hAB : kimberlingOnePosition 3 = 4 :=
    kimberlingOnePosition_eq_succ_of_count (n := 2) (i := 3) (by decide) (by decide)
  rw [hB, hA, hAB]

-- Count directly again: A₄ = 5, B₄ = 14, and A₁₄ = 18, giving the off-by-one case.
example : kimberlingOnePosition (kimberlingZeroPosition 4) + 1 =
    kimberlingOnePosition 4 + kimberlingZeroPosition 4 := by
  have hA : kimberlingOnePosition 4 = 5 :=
    kimberlingOnePosition_eq_succ_of_count (n := 3) (i := 4) (by decide) (by decide)
  have hB : kimberlingZeroPosition 4 = 14 :=
    kimberlingZeroPosition_eq_succ_of_count (n := 3) (i := 13)
      (by decide +kernel) (by decide +kernel)
  have hAB : kimberlingOnePosition 14 = 18 :=
    kimberlingOnePosition_eq_succ_of_count (n := 13) (i := 17)
      (by decide +kernel) (by decide +kernel)
  rw [hB, hA, hAB]

example : kimberlingOnePosition (kimberlingZeroPosition 2) + 1 =
      kimberlingOnePosition 2 + kimberlingZeroPosition 2 ∨
    kimberlingOnePosition (kimberlingZeroPosition 2) =
      kimberlingOnePosition 2 + kimberlingZeroPosition 2 :=
  kimberlingOnePosition_kimberlingZeroPosition (by decide)
