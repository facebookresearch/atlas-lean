/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.DisjunctiveRadoSingleton

/-! # Tests for the singleton Rado number -/

open MathlibExt.Combinatorics.DisjunctiveRadoWanted

-- The result includes the endpoint `m = a = 4`.
example : IsLeast (disjRadoSet 4 4 {5}) 1 :=
  isLeast_disjRadoSet_eq_one 4 4 (by decide) (by decide)

-- With `4 < m < a`, the bound `1` is admissible but `0` is not.
example : (1 : ℕ) ∈ disjRadoSet 6 9 {12} ∧ 0 ∉ disjRadoSet 6 9 {12} := by
  have h : IsLeast (disjRadoSet 6 9 {12}) 1 :=
    isLeast_disjRadoSet_eq_one 9 6 (by decide) (by decide)
  exact ⟨h.1, fun h0 => (by decide : ¬ (1 : ℕ) ≤ 0) (h.2 h0)⟩
