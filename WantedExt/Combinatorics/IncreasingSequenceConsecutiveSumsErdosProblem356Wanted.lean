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

/-- **Consecutive sums.** Let $k \in \mathbb{N}$ and let $a_0, \dots, a_{k-1}$ be natural
numbers. The consecutive sums of $a$ form the finite set of natural numbers
$a_u + a_{u+1} + \dots + a_v$ for indices $0 \le u \le v \le k - 1$. -/
def consecutiveSums {k : ℕ} (a : Fin k → ℕ) : Finset ℕ :=
  ((Finset.univ : Finset (Fin k × Fin k)).filter fun p => p.1 ≤ p.2).image
    fun p => ∑ i ∈ Finset.Icc p.1 p.2, a i

/-- **Erdős Problem 356.** The proposition that there is a real number $c > 0$ such that for all
sufficiently large $n \in \mathbb{N}$ there exist $k \in \mathbb{N}$ and natural numbers
$a_0 < a_1 < \dots < a_{k-1}$ with $1 \le a_i \le n$ for every $i$, whose set of consecutive sums
$a_u + a_{u+1} + \dots + a_v$ (for $u \le v$) has at least $c n^2$ elements. -/
def manyDistinctConsecutiveSums : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in Filter.atTop, ∃ k : ℕ, ∃ a : Fin k → ℕ, StrictMono a ∧
    (∀ i, 1 ≤ a i ∧ a i ≤ n) ∧ c * (n : ℝ) ^ 2 ≤ (consecutiveSums a).card

/--
**Erdős Problem 356 has a positive answer.** There is a real number $c > 0$ such that for all
sufficiently large $n \in \mathbb{N}$ there exist $k \in \mathbb{N}$ and natural numbers
$a_0 < a_1 < \dots < a_{k-1}$ with $1 \le a_i \le n$ for every $i$, whose set of consecutive sums
$a_u + a_{u+1} + \dots + a_v$ (for $u \le v$) has at least $c n^2$ elements.

Source: T. F. Bloom,
Erdős Problems, Problem #356, https://www.erdosproblems.com/356 (status PROVED (LEAN)); resolution:
A. Beker, On a problem of Erdős and Graham about consecutive sums in strictly increasing sequences,
arXiv:2311.10087 (2023), erdosproblems.com/356: the original problem was solved in the affirmative
by Beker, https://arxiv.org/abs/2311.10087.
-/
public theorem_wanted manyDistinctConsecutiveSums_holds : manyDistinctConsecutiveSums

end MathlibExt.Combinatorics.IncreasingSequenceConsecutiveSumsErdosProblem356Wanted
