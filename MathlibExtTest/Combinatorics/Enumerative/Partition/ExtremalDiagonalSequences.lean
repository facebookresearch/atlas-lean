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

-- The class of `(3, 1)` is `{(3, 1), (2, 2), (2, 1, 1)}`: a single factor `C(3, 2)`.
example : (diagonalClass (Nat.Partition.ofMultiset {3, 1})).card = 3 := by
  rw [card_diagonalClass_eq_prod_choose _ 2 3 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)]
  decide +kernel

-- The paper's running example `(7, 7, 4, 1, 1, 1)` has 36 partitions in its class; the zero
-- drops after the staircase give factors `1` and `3`.
example : (diagonalClass (Nat.Partition.ofMultiset {7, 7, 4, 1, 1, 1})).card = 36 := by
  rw [card_diagonalClass_eq_prod_choose _ 4 8 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)]
  decide +kernel

-- A staircase is alone in its class: `q = L` and the product is empty.
example : (diagonalClass (Nat.Partition.ofMultiset {3, 2, 1})).card = 1 := by
  rw [card_diagonalClass_eq_prod_choose _ 3 3 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)]
  rfl

-- The single part `1` is the smallest staircase, with `q = L = 1`.
example : (diagonalClass (Nat.Partition.ofMultiset {1})).card = 1 := by
  rw [card_diagonalClass_eq_prod_choose _ 1 1 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)]
  rfl

-- The row `(3)` shares its class only with the column `(1, 1, 1)`.
example : (diagonalClass (Nat.Partition.ofMultiset {3})).card = 2 := by
  rw [card_diagonalClass_eq_prod_choose _ 1 3 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)]
  decide +kernel

-- The class of `(4, 3, 2)` has four elements, the last case of the paper's Corollary 7 (4).
example : (diagonalClass (Nat.Partition.ofMultiset {4, 3, 2})).card = 4 := by
  rw [card_diagonalClass_eq_prod_choose _ 3 4 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)]
  decide +kernel

end MetaMathlibExt
