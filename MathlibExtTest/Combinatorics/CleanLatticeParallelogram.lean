/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.CleanLatticeParallelogram

/-! # Tests for the integer heights of vertical columns -/

open MetaMathlibExt

-- The smallest admissible parallelogram has just one interior height.
example : stdColumn 1 2 1 = {1} := by
  obtain ⟨hl, hu⟩ := (stdColumn_least_greatest (a := 1) (n := 2)
    (by decide) (by decide) (by decide)).1 rfl
  ext y
  simp only [Set.mem_singleton_iff]
  constructor
  · intro hy
    exact le_antisymm (show y ≤ 1 from hu.2 hy) (hl.2 hy)
  · rintro rfl
    exact hl.1

-- The middle column has nonintegral crossings at 8/3 and 16/3.
-- The first and last columns exclude the boundary heights 0 and 8.
example :
    (IsLeast (stdColumn 3 8 1) 1 ∧ IsGreatest (stdColumn 3 8 1) 2) ∧
    (IsLeast (stdColumn 3 8 2) 3 ∧ IsGreatest (stdColumn 3 8 2) 5) ∧
    (IsLeast (stdColumn 3 8 3) 6 ∧ IsGreatest (stdColumn 3 8 3) 7) := by
  obtain ⟨middle, firstLow, firstHigh, lastLow, lastHigh⟩ :=
    (stdColumn_least_greatest (a := 3) (n := 8) (by decide) (by decide) (by decide)).2 (by decide)
  have mid := middle 2 (by decide) (by decide)
  norm_num [Rat.floor_natCast_div_natCast, Rat.ceil_natCast_div_natCast] at firstHigh mid lastLow
  exact ⟨⟨firstLow, firstHigh⟩, mid, lastLow, lastHigh⟩
