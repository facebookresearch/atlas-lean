/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ErdosProblem844

/-! # Tests for Erdős Problem 844 -/

namespace MathlibExt.NumberTheory.ErdosProblem844Wanted

-- The extremal set for `N = 10`: the even numbers together with the odd non-squarefree `9`.
example : evenOrOddNonSquarefree 10 = {2, 4, 6, 8, 9, 10} := by decide +kernel

-- `1` never belongs to the extremal set, matching the case `a = b = 1` of the condition.
example (N : ℕ) : 1 ∉ evenOrOddNonSquarefree N := by
  simp [evenOrOddNonSquarefree]

-- No set in `{1, ..., 10}` whose pairwise products (squares included) are non-squarefree has more
-- than six elements.
example (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 10)
    (h : ∀ a ∈ A, ∀ b ∈ A, ¬ Squarefree (a * b)) : A.card ≤ 6 := by
  have hbound := (conjecture_holds 10).2 ⟨A, hA, h, rfl⟩
  rwa [show (evenOrOddNonSquarefree 10).card = 6 by decide +kernel] at hbound

-- The bound for `N = 10` is attained.
example : ∃ A ⊆ Finset.Icc 1 10, (∀ a ∈ A, ∀ b ∈ A, ¬ Squarefree (a * b)) ∧ A.card = 6 := by
  have hmem := (conjecture_holds 10).1
  rwa [show (evenOrOddNonSquarefree 10).card = 6 by decide +kernel] at hmem

-- For `N = 1` the bound is `0`: the set `{1}` is excluded because `1 * 1` is squarefree.
example (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 1)
    (h : ∀ a ∈ A, ∀ b ∈ A, ¬ Squarefree (a * b)) : A = ∅ := by
  have hbound := (conjecture_holds 1).2 ⟨A, hA, h, rfl⟩
  rw [show evenOrOddNonSquarefree 1 = ∅ by decide +kernel] at hbound
  simpa using hbound

end MathlibExt.NumberTheory.ErdosProblem844Wanted
