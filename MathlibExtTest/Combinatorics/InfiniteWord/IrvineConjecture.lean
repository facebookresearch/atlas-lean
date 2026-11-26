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
