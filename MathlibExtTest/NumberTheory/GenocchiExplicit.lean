/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.GenocchiExplicit
import Mathlib.Tactic.NormNum

open MathlibExt.NumberTheory.GenocchiExplicitWanted

-- At k = j = 0 the factorial argument truncates to zero.
example : zerroU 0 0 = 1 := by
  norm_num [zerroU]

-- The first step at the smallest admissible k uses the row r = 0.
example : zerroU 1 1 = -1 / 2 := by
  rw [zerroU_succ 0 1 (by decide)]
  norm_num [zerroU]

-- In this step both terms contribute, and the second has multiplicity two.
example : zerroU 3 2 = -1 / 4 := by
  rw [zerroU_succ 2 2 (by decide)]
  norm_num [zerroU, Finset.sum_range_succ, Nat.factorial, Nat.stirlingSecond]
