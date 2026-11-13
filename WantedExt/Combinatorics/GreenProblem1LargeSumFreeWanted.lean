/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Green Problem 1: large sum-free subsets
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Finset.Card
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic

@[expose] public section

namespace MathlibExt.Combinatorics.GreenProblem1LargeSumFreeWanted

/-! Source record `GREEN-001__92`. -/

/-- A finite set of natural numbers is sum-free: no sum of two (not necessarily
distinct) members lies in the set [GREEN-001]. -/
def IsSumFree (s : Finset ℕ) : Prop :=
  ∀ x ∈ s, ∀ y ∈ s, x + y ∉ s

/-- Large sum-free subset question from [GREEN-001] (Ben Green, Problem 1):
there exists an unbounded function `ω`, with `ω(n) → ∞` as `n → ∞`, such that
every finite set `A` of positive integers contains a sum-free subset `B ⊆ A`
of size at least `|A| / 3 + ω(|A|)`. -/
def conjecture : Prop :=
  ∃ ω : ℕ → ℝ, Filter.Tendsto ω Filter.atTop Filter.atTop ∧
    ∀ (A : Finset ℕ), (∀ a ∈ A, 0 < a) →
      ∃ B : Finset ℕ, B ⊆ A ∧ IsSumFree B ∧
        (A.card : ℝ) / 3 + ω (A.card) ≤ (B.card : ℝ)

/--
Resolved true: Resolved affirmatively by Bedert, who proves that every n-element set of integers
contains a sum-free subset of size at least n/3 + c log log n for an absolute constant c > 0.
Source: Benjamin Bedert, Large sum-free subsets of sets of integers via L¹-estimates for
trigonometric series, arXiv:2502.08624v1, https://arxiv.org/abs/2502.08624v1. Moved from
`OpenConjectures/Combinatorics/GreenProblem1LargeSumFree`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Combinatorics.GreenProblem1LargeSumFreeWanted
