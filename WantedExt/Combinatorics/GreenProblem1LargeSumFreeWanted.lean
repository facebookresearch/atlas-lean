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
public import Mathlib.Data.Real.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic

@[expose] public section

namespace MathlibExt.Combinatorics.GreenProblem1LargeSumFreeWanted

/-! Source record `GREEN-001__92`. -/

/-- **Sum-free sets of natural numbers.** A finite set $S$ of natural numbers is sum-free if
$x + y \notin S$ for all $x, y \in S$, where $x = y$ is allowed.

Source: [GREEN-001]. -/
def IsSumFree (s : Finset ℕ) : Prop :=
  ∀ x ∈ s, ∀ y ∈ s, x + y ∉ s

/-- **Green's Problem 1 on large sum-free subsets.** The statement that there is a function
$\omega$ from the natural numbers to the real numbers with $\omega(n) \to \infty$ as
$n \to \infty$ such that every finite set $A$ of positive integers contains a sum-free subset
$B \subseteq A$ with $|B| \ge |A|/3 + \omega(|A|)$.

Source: Ben Green, Problem 1 [GREEN-001]. -/
def conjecture : Prop :=
  ∃ ω : ℕ → ℝ, Filter.Tendsto ω Filter.atTop Filter.atTop ∧
    ∀ (A : Finset ℕ), (∀ a ∈ A, 0 < a) →
      ∃ B : Finset ℕ, B ⊆ A ∧ IsSumFree B ∧
        (A.card : ℝ) / 3 + ω (A.card) ≤ (B.card : ℝ)

/--
**Bedert's theorem on large sum-free subsets.** There is a function $\omega$ from the natural
numbers to the real numbers with $\omega(n) \to \infty$ as $n \to \infty$ such that every finite
set $A$ of positive integers contains a subset $B \subseteq A$ with $x + y \notin B$ for all
$x, y \in B$ (a sum-free subset) and $|B| \ge |A|/3 + \omega(|A|)$.

Bedert proves more: every $n$-element set of integers contains a sum-free subset of size at least
$n/3 + c \log \log n$ for an absolute constant $c > 0$. This answers Green's Problem 1.

Source: Benjamin Bedert, Large sum-free subsets of sets of integers via L¹-estimates for
trigonometric series, arXiv:2502.08624v1, https://arxiv.org/abs/2502.08624v1. Moved from
`OpenConjectures/Combinatorics/GreenProblem1LargeSumFree`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Combinatorics.GreenProblem1LargeSumFreeWanted
