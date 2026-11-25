/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.Partition.ExtremalDiagonalSequences

namespace MetaMathlibExt

-- The empty partition gives zero even at indices beyond the length of the normal form.
example (s : ℕ → ℕ) (k : ℕ) : diagonalSequence ↑(diagonalMaxPartition 0 s) k = 0 := by
  obtain ⟨h, hmin, _⟩ := diagonalSequence_max_eq_min_and_multiset 0 s
  rw [h, hmin]
  cases k <;> rfl

-- The four-row example skips the block of threes and repeats the largest height.
example :
    diagonalSequence ↑([8, 6, 4, 3] : List ℕ) =
      diagonalOfList [1, 2, 3, 4, 4, 4, 2, 1] ∧
    diagonalSequence ↑([4, 4, 4, 3, 2, 2, 1, 1] : List ℕ) =
      diagonalOfList [1, 2, 3, 4, 4, 4, 2, 1] ∧
    ([1, 2, 3, 4, 4, 4, 2, 1] : Multiset ℕ) = ↑([4, 4, 4, 3, 2, 2, 1, 1] : List ℕ) := by
  obtain ⟨h, hmin, hparts⟩ :=
    diagonalSequence_max_eq_min_and_multiset 4 (fun k => [0, 1, 1, 0, 2].getD k 0)
  simpa only [diagonalMaxPartition_four_example, diagonalMinPartition_four_example,
    diagonalNormalForm_four_example] using And.intro (h.trans hmin) (And.intro hmin hparts)

end MetaMathlibExt
