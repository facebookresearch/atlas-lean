/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.CatalanTable

open MetaMathlibExt

/-- The table at `0` is `[1]`. -/
example : catalanTable 0 = [1] := rfl

/-- Entries `2`, `3` and `4` are computed by the recurrence from the earlier entries. -/
example : catalanTable 4 = [1, 1, 2, 5, 14] := by decide

/-- Values read off the table at recursive indices. -/
example : catalanDP 2 = 2 := by decide

example : catalanDP 10 = 16796 := by decide

/-- The correctness theorem turns a `decide` computation into a value of `catalan`. -/
example : catalan 5 = 42 := by
  rw [← catalanDP_eq_catalan]
  decide
