/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum
import MathlibExt.Combinatorics.Additive.UnionTwoAPNotMSTD

open MetaMathlibExt

/-- The smallest instance of the hypotheses is the set $\{0, 1, 2, 3, 5, 7\}$, whose
progression starts at $x = n$, directly after the interval. -/
example : realIntervalSet 3 ∪ realAPSet 3 2 2 = {0, 1, 2, 3, 5, 7} := by
  ext y
  simp only [realIntervalSet, realAPSet, Finset.range_add_one, Finset.range_zero,
    Finset.image_insert, Finset.image_empty, Finset.mem_union, Finset.mem_insert,
    Finset.mem_singleton, Finset.notMem_empty, or_false]
  norm_num only [or_comm, or_left_comm, or_assoc]

/-- The smallest instance of the hypotheses, $I_3 \cup J(3, 2, 2)$, is not an MSTD set. -/
example : ¬ IsMSTDSet (realIntervalSet 3 ∪ realAPSet 3 2 2) := by
  simpa using not_isMSTDSet_intervalAP_nat_of_lt 3 2 2 3 le_rfl le_rfl le_rfl (by decide)

/-- A progression starting far after the interval, with step larger than the interval, is
covered as well. -/
example : ¬ IsMSTDSet (realIntervalSet 4 ∪ realAPSet 9 3 5) := by
  simpa using not_isMSTDSet_intervalAP_nat_of_lt 4 3 5 9 (by decide) (by decide) (by decide)
    (by decide)
