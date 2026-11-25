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

-- `IsWellBased` can be constructed from the split condition alone, even for `{0}`.
example : IsWellBased ({0} : Finset ℕ) := by
  intro x hx a ha hax
  have hx0 := Finset.mem_singleton.mp hx
  omega

example (ω l : ℕ) (hω : ω < 2 ^ l) (x : ℕ) (hx : x ∈ subwordShiftSet ω l)
    (a : ℕ) (ha : 0 < a) (hax : a < x) :
    a ∈ subwordShiftSet ω l ∨ x - a ∈ subwordShiftSet ω l :=
  isWellBased_subwordShiftSet ω l hω x hx a ha hax

example : ¬ IsPositiveWellBased ({0} : Finset ℕ) :=
  fun h => h.1 (by simp)

example : IsPositiveWellBased ∅ := by
  simp [IsPositiveWellBased, IsWellBased]

example (ω l : ℕ) : 0 ∉ subwordShiftSet ω l :=
  zero_notMem_subwordShiftSet ω l

example (ω l : ℕ) (hl : l ≤ 1) : subwordShiftSet ω l = ∅ := by
  ext j
  simp only [subwordShiftSet, Finset.mem_filter, Finset.mem_Icc, Finset.notMem_empty,
    iff_false]
  omega

example : IsPositiveWellBased (subwordShiftSet 0 0) :=
  isPositiveWellBased_subwordShiftSet 0 0 (by decide)

example : IsPositiveWellBased (subwordShiftSet 1 1) :=
  isPositiveWellBased_subwordShiftSet 1 1 (by decide)

example : IsPositiveWellBased ({1, 3} : Finset ℕ) := by
  rw [← subwordShiftSet_1010]
  exact isPositiveWellBased_subwordShiftSet 0b1010 4 (by decide)

-- The stronger clause fails: the omitted shifts 5 and 7 have difference 2 in Q.
example : subwordShiftSet 0b010100101 9 = {1, 2, 3, 4, 6, 8} := by decide

example : 5 ∉ subwordShiftSet 0b010100101 9 ∧ 7 ∉ subwordShiftSet 0b010100101 9 ∧
    7 - 5 ∈ subwordShiftSet 0b010100101 9 := by decide

end MetaMathlibExt
