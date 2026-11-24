/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.Partition.ConsecutiveVnArrangements

open MetaMathlibExt

-- The shortest interval has one ordering.
example (a : ℤ) : vnArrangementCount 1 (Finset.Ico a (a + 1)).val = 1 :=
  vnArrangementCount_consecutive a 1 (by decide)

-- Four of the six permutations of the interval crossing zero satisfy the step bound.
example : vnArrangementCount 1 ({-1, 0, 1} : Multiset ℤ) = 4 := by
  have h : (Finset.Ico (-1 : ℤ) 2).val = {-1, 0, 1} := by decide
  rw [← h]
  exact vnArrangementCount_consecutive (-1) 3 (by decide)
