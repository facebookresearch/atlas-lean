/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Additive.IntervalEraseAddSub

open scoped Pointwise
open MetaMathlibExt

-- The smallest admissible interval has just one choice of erased point.
example :
    let B := ({0, 1, 3, 4} : Finset ℤ)
    B + B = Finset.Icc 0 8 ∧ B - B = Finset.Icc (-4) 4 := by
  have hB : (Finset.Icc 0 ((5 : ℤ) - 1)).erase 2 = {0, 1, 3, 4} := by decide
  have h := interval_erase_add_sub (m := 5) (r := 2) (by decide) (by decide) (by decide)
  rw [hB] at h
  simpa only [Int.reduceMul, Int.reduceSub] using h

-- Erasing a neighbor of either endpoint loses the sum next to the corresponding extreme.
example :
    let B := (Finset.Icc (0 : ℤ) 4).erase 1
    1 ∉ B + B := by decide

example :
    let B := (Finset.Icc (0 : ℤ) 4).erase 3
    7 ∉ B + B := by decide
