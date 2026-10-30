/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Many distinct consecutive sums of an increasing sequence (Erdős Problem 356)

Erdős Problem 356: is there `c > 0` such that, for all large `n`, there are integers `a₁ < ⋯ < a_k ≤
n` with at least `c n²` distinct sums `∑_{u ≤ i ≤ v} aᵢ`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Interval.Finset.Fin

@[expose] public section

namespace MathlibExt.Combinatorics.IncreasingSequenceConsecutiveSumsErdosProblem356Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #356, https://www.erdosproblems.com/356 (status PROVED
(LEAN)). UnsolvedMath record UM-30006836 (`EP-356`), dataset ulamai/UnsolvedMath v1.8.0.

The `aᵢ` are positive integers (with negative terms the length `k` would be unbounded and the
question trivial) and `k` is arbitrary. Consecutive sums are taken over index intervals `u ≤ v` and
counted as distinct values. formal-conjectures has no statement of this problem.
-/

/-- The sums `a u + ⋯ + a v` (`u ≤ v`) of consecutive terms of `a 0, …, a (k - 1)`. -/
def consecutiveSums {k : ℕ} (a : Fin k → ℕ) : Finset ℕ :=
  ((Finset.univ : Finset (Fin k × Fin k)).filter fun p => p.1 ≤ p.2).image
    fun p => ∑ i ∈ Finset.Icc p.1 p.2, a i

/-- Erdős Problem 356: there is `c > 0` such that for all large `n` some integers
`1 ≤ a₁ < ⋯ < a_k ≤ n` have at least `c n²` distinct sums of consecutive terms. -/
def manyDistinctConsecutiveSums : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in Filter.atTop, ∃ k : ℕ, ∃ a : Fin k → ℕ, StrictMono a ∧
    (∀ i, 1 ≤ a i ∧ a i ≤ n) ∧ c * (n : ℝ) ^ 2 ≤ (consecutiveSums a).card

/--
Resolved true: Beker proved that for all large `n` some `1 ≤ a₁ < ⋯ < a_k ≤ n` have `≫ n²` distinct
sums of consecutive terms; erdosproblems.com/356 lists the problem as proved. Source: T. F. Bloom,
Erdős Problems, Problem #356, https://www.erdosproblems.com/356 (status PROVED (LEAN)); resolution:
A. Beker, On a problem of Erdős and Graham about consecutive sums in strictly increasing sequences,
arXiv:2311.10087 (2023), erdosproblems.com/356: the original problem was solved in the affirmative
by Beker, https://arxiv.org/abs/2311.10087.
-/
public theorem_wanted manyDistinctConsecutiveSums_holds : manyDistinctConsecutiveSums

end MathlibExt.Combinatorics.IncreasingSequenceConsecutiveSumsErdosProblem356Wanted
