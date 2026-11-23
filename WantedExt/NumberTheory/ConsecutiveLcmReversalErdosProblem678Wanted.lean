/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Least common multiples of consecutive integers out of order (Erdős Problem 678)

Erdős Problem 678: let `M(n, k) = [n + 1, …, n + k]` be the least common multiple of `{n + 1, …, n +
k}`. Are there infinitely many `m, n` and `k ≥ 3` with `m ≥ n + k` such that `M(n, k) > M(m, k +
1)`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

namespace MathlibExt.NumberTheory.ConsecutiveLcmReversalErdosProblem678Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #678, https://www.erdosproblems.com/678 (status PROVED
(LEAN)). UnsolvedMath record UM-30006979 (`EP-678`), dataset ulamai/UnsolvedMath v1.8.0.

"Infinitely many `m, n` and `k`" is read as infinitely many triples `(m, n, k)`: for a fixed `k`
only finitely many pairs exist (see the problem page), so the infinitude ranges over `k` as well. A
second target states Cambie's stronger theorem. Compared with the formal-conjectures statement
`ErdosProblems/678.lean` (the first target is `erdos_678.variants.infinitely_many_triples`; no code
imported).
-/

/-- `M(n, k) = [n + 1, …, n + k]`, the least common multiple of `n + 1, …, n + k`. -/
def lcmInterval (n k : ℕ) : ℕ :=
  (Finset.Icc (n + 1) (n + k)).lcm id

/-- Erdős Problem 678: there are infinitely many triples `(m, n, k)` with `k ≥ 3` and
`m ≥ n + k` such that `M(n, k) > M(m, k + 1)`. -/
def infinitelyManyLcmReversals : Prop :=
  {t : ℕ × ℕ × ℕ | 3 ≤ t.2.2 ∧ t.2.1 + t.2.2 ≤ t.1 ∧
    lcmInterval t.1 (t.2.2 + 1) < lcmInterval t.2.1 t.2.2}.Infinite

/-- Cambie's strong form: for every constant `C` and every sufficiently large `k` there are
`m > n + k` with `M(n, k) > C · M(m, k + 1)`. -/
def lcmReversalArbitraryRatio : Prop :=
  ∀ C : ℕ, ∀ᶠ k : ℕ in Filter.atTop, ∃ m n : ℕ, n + k < m ∧
    C * lcmInterval m (k + 1) < lcmInterval n k

/--
Resolved true: Cambie proved that for every sufficiently large `k` there are `m > n + k` with `M(n,
k) > M(m, k + 1)` (Theorem 1 with `C = 1`, `x = n + 1`, `y = m + 1`), which gives infinitely many
triples; erdosproblems.com/678 lists the problem as proved. Source: T. F. Bloom, Erdős Problems,
Problem #678, https://www.erdosproblems.com/678 (status PROVED (LEAN)); resolution: S. Cambie,
Resolution of an Erdős' problem on least common multiples, arXiv:2410.09138 (2024), Theorem 1: for
every constant C ≥ 1 and every sufficiently large k there are integers 0 < x < y with y > x + k and
lcm{x, …, x + k - 1} > C · lcm{y, …, y + k}; erdosproblems.com/678: the answer is yes,
https://arxiv.org/abs/2410.09138.
-/
public theorem_wanted infinitelyManyLcmReversals_holds : infinitelyManyLcmReversals

/--
Resolved true: Cambie's Theorem 1: for every constant `C` and every sufficiently large `k` there are
integers `0 < x < y` with `y > x + k` and `lcm{x, …, x + k - 1} > C · lcm{y, …, y + k}`; with `x = n
+ 1` and `y = m + 1` this is `M(n, k) > C · M(m, k + 1)` with `m > n + k`. Source: T. F. Bloom,
Erdős Problems, Problem #678, https://www.erdosproblems.com/678 (status PROVED (LEAN)); resolution:
S. Cambie, Resolution of an Erdős' problem on least common multiples, arXiv:2410.09138 (2024),
Theorem 1: for every constant C ≥ 1 and every sufficiently large k there are integers 0 < x < y with
y > x + k and lcm{x, …, x + k - 1} > C · lcm{y, …, y + k}; erdosproblems.com/678: the answer is yes,
https://arxiv.org/abs/2410.09138.
-/
public theorem_wanted lcmReversalArbitraryRatio_holds : lcmReversalArbitraryRatio

end MathlibExt.NumberTheory.ConsecutiveLcmReversalErdosProblem678Wanted
