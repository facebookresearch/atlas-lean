/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Rough numbers between consecutive primes (Erdős Problem 682)

Erdős Problem 682: is it true that for almost all `n` there exists some `m ∈ (p_n, p_{n+1})` such
that `p(m) ≥ p_{n+1} - p_n`, where `p(m)` denotes the least prime factor of `m`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.Nth
public import MathlibExt.Data.Set.Density

@[expose] public section

namespace MathlibExt.NumberTheory.RoughNumberPrimeGapErdosProblem682Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #682, https://www.erdosproblems.com/682 (status
PROVED). UnsolvedMath record UM-30006980 (`EP-682`), dataset ulamai/UnsolvedMath v1.8.0.

"Almost all" means natural density `1` (`Set.HasDensity`, MathlibExt). `p_n` is `Nat.nth Nat.Prime
n` (indexed from `p_0 = 2`; the shift does not affect density statements) and `p(m)` is `Nat.minFac
m`. Compared with the formal-conjectures statement `ErdosProblems/682.lean` (equivalent; no code
imported).
-/

/-- Erdős Problem 682: for almost all `n` (a set of indices of natural density `1`) there is an
integer `m` with `p_n < m < p_{n+1}` whose least prime factor is at least `p_{n+1} - p_n`; here
`p_n = Nat.nth Nat.Prime n` is the `n`-th prime (indexed from `p_0 = 2`). -/
def roughNumberInAlmostAllPrimeGaps : Prop :=
  {n : ℕ | ∃ m : ℕ, Nat.nth Nat.Prime n < m ∧ m < Nat.nth Nat.Prime (n + 1) ∧
    Nat.nth Nat.Prime (n + 1) - Nat.nth Nat.Prime n ≤ m.minFac}.HasDensity 1

/--
Resolved true: Gafni and Tao proved that almost all gaps `(p_n, p_{n+1})` contain an integer `m`
with least prime factor at least `p_{n+1} - p_n`; the number of exceptional gaps with `p_n ∈ [X,
2X]` is `O(X / log² X)`. erdosproblems.com/682 lists the problem as proved. Source: T. F. Bloom,
Erdős Problems, Problem #682, https://www.erdosproblems.com/682 (status PROVED); resolution: A.
Gafni and T. Tao, Rough numbers between consecutive primes, arXiv:2508.06463 (2025), abstract:
almost all gaps (p_n, p_{n+1}) contain a natural number m whose least prime factor is at least
p_{n+1} - p_n; the number of exceptional gaps with p_n ∈ [X, 2X] is O(X / log² X);
erdosproblems.com/682: solved in the affirmative by Gafni and Tao, https://arxiv.org/abs/2508.06463.
-/
public theorem_wanted roughNumberInAlmostAllPrimeGaps_holds : roughNumberInAlmostAllPrimeGaps

end MathlibExt.NumberTheory.RoughNumberPrimeGapErdosProblem682Wanted
