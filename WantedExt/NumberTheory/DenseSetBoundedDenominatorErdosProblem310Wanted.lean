/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Unit sums with bounded denominators in dense sets (Erdős Problem 310)

Erdős Problem 310: let `α > 0` and `N ≥ 1`. Is it true that every `A ⊆ {1, …, N}` with `|A| ≥ α N`
has `S ⊆ A` with `∑_{n ∈ S} 1/n = a/b`, `a ≤ b = O_α(1)`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

namespace MathlibExt.NumberTheory.DenseSetBoundedDenominatorErdosProblem310Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #310, https://www.erdosproblems.com/310 (status PROVED
(LEAN)); P. Erdős and R. L. Graham, Old and new problems and results in combinatorial number theory
(1980). UnsolvedMath record UM-30006821 (`EP-310`), dataset ulamai/UnsolvedMath v1.8.0.

`S = ∅` would give `0 = 0/1`, so the sum is required to be positive (`0 < a`). `O_α(1)` is a bound
`B(α)` independent of `N`. Compared with the formal-conjectures statement `ErdosProblems/310.lean`
(identical statement; no code imported).
-/

/-- Erdős Problem 310: for every `α > 0` there is `B` such that for all `N ≥ 1`, every
`A ⊆ {1, …, N}` with `|A| ≥ α N` has `S ⊆ A` with `∑_{n ∈ S} 1/n = a/b`, `0 < a ≤ b ≤ B`. -/
def denseSetBoundedDenominatorSum : Prop :=
  ∀ α : ℝ, 0 < α → ∃ B : ℕ, ∀ N : ℕ, 1 ≤ N → ∀ A ⊆ Finset.Icc 1 N, α * N ≤ A.card →
    ∃ S ⊆ A, ∃ a b : ℕ, 0 < a ∧ a ≤ b ∧ b ≤ B ∧ ∑ n ∈ S, (1 : ℚ) / n = a / b

/--
Resolved true: Liu and Sawhney observed that Bloom's density theorem implies the claim and proved it
with `b ≤ exp(O(1/α))`. erdosproblems.com/310 lists the problem as proved. Source: T. F. Bloom,
Erdős Problems, Problem #310, https://www.erdosproblems.com/310 (status PROVED (LEAN)); P. Erdős and
R. L. Graham, Old and new problems and results in combinatorial number theory (1980); resolution: Y.
P. Liu and M. Sawhney, On further questions regarding unit fractions, arXiv:2404.07113 (2024); T. F.
Bloom, On a density conjecture about unit fractions, arXiv:2112.03726 (2021); formalized in Lean 3
by T. F. Bloom and B. Mehta (github.com/b-mehta/unit-fractions), Proposition 1.4 and the remark
after it (a direct application of Proposition 1 of [Bl21] gives b = O_α(1)); erdosproblems.com/310:
Liu and Sawhney observed that the main result of Bloom [Bl21] implies a positive answer, and proved
b ≤ exp(O(1/α)) for (log N)^{-1/7+o(1)} ≤ α ≤ 1/2, https://www.erdosproblems.com/310.
-/
public theorem_wanted denseSetBoundedDenominatorSum_holds : denseSetBoundedDenominatorSum

end MathlibExt.NumberTheory.DenseSetBoundedDenominatorErdosProblem310Wanted
