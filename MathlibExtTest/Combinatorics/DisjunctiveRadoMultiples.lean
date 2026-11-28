/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.DisjunctiveRadoMultiples

/-! # Tests for the disjunctive Rado number of two multiples -/

open MathlibExt.Combinatorics.DisjunctiveRadoWanted

-- The smaller multiplier is the first one, with `m = a = 4`.
example : IsLeast (disjRadoSet 4 4 {10, 30}) 2 :=
  isLeast_disjRadoSet_multiples 4 4 2 6 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)

-- The second multiplier is smaller. The threshold works, but its predecessor does not.
example : (3 : ℕ) ∈ disjRadoSet 5 7 {90, 27} ∧ 2 ∉ disjRadoSet 5 7 {90, 27} := by
  have h : IsLeast (disjRadoSet 5 7 {90, 27}) 3 :=
    isLeast_disjRadoSet_multiples 7 5 10 3 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)
  exact ⟨h.1, fun h₂ => (by decide : ¬ (3 : ℕ) ≤ 2) (h.2 h₂)⟩

-- Tied multipliers can both attain the upper endpoint.
example : IsLeast (disjRadoSet 4 4 {30, 30}) 6 :=
  isLeast_disjRadoSet_multiples 4 4 6 6 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)
