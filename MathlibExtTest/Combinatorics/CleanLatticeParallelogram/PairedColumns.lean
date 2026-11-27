/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.CleanLatticeParallelogram.PairedColumns

/-! # Tests for reflection of extremal points on paired columns -/

open MetaMathlibExt

-- The bottom of the first column determines the top of the last column.
example {yH : ℤ} (hH : IsGreatest (stdColumn 3 8 3) yH) :
    let B := frontier (convexHull ℝ (interior (stdCleanParallelogram 3 8) ∩ latticePoints))
    yH = 7 ∧ ((3, (yH : ℝ)) ∈ B ↔ (1, 1) ∈ B) := by
  obtain ⟨_, firstLow, _⟩ :=
    (stdColumn_least_greatest (a := 3) (n := 8) (by decide) (by decide) (by decide)).2 (by decide)
  obtain ⟨hsum, hfrontier⟩ := stdColumn_low_add_high (k := 1) (l := 3)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) firstLow hH
  exact ⟨by omega, by simpa using hfrontier⟩

-- The middle column is paired with itself, but its extremal heights are distinct.
example :
    let B := frontier (convexHull ℝ (interior (stdCleanParallelogram 3 8) ∩ latticePoints))
    (2, 5) ∈ B ↔ (2, 3) ∈ B := by
  have ⟨low, high⟩ := ((stdColumn_least_greatest (a := 3) (n := 8)
    (by decide) (by decide) (by decide)).2 (by decide)).1 2 (by decide) (by decide)
  norm_num [Rat.ceil_natCast_div_natCast, Rat.floor_natCast_div_natCast] at low high
  simpa using (stdColumn_low_add_high (k := 2) (l := 2)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) low high).2
