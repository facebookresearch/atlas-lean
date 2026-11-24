/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.SubwordShiftSet

/-! # Tests for well-based binary subword shift sets -/

namespace MetaMathlibExt

-- Positivity rules out the vacuous singleton even though there is no positive split of zero.
example : ¬ IsWellBased ({0} : Finset ℕ) := by
  intro h
  exact h.1 (by simp)

example : IsWellBased (∅ : Finset ℕ) := by
  simp [IsWellBased]

example (ω l : ℕ) (hl : l ≤ 1) : subwordShiftSet ω l = ∅ := by
  ext j
  simp only [subwordShiftSet, Finset.mem_filter, Finset.mem_Icc, Finset.notMem_empty,
    iff_false]
  omega

example : IsWellBased (subwordShiftSet 0 0) :=
  isWellBased_subwordShiftSet 0 0 (by decide)

example : IsWellBased (subwordShiftSet 1 1) :=
  isWellBased_subwordShiftSet 1 1 (by decide)

example : IsWellBased ({1, 3} : Finset ℕ) := by
  rw [← subwordShiftSet_1010]
  exact isWellBased_subwordShiftSet 0b1010 4 (by decide)

-- The stronger clause fails: the omitted shifts 5 and 7 have difference 2 in Q.
example : subwordShiftSet 0b010100101 9 = {1, 2, 3, 4, 6, 8} := by decide

example : 5 ∉ subwordShiftSet 0b010100101 9 ∧ 7 ∉ subwordShiftSet 0b010100101 9 ∧
    7 - 5 ∈ subwordShiftSet 0b010100101 9 := by decide

end MetaMathlibExt
