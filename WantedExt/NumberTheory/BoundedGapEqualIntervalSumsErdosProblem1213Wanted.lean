/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Equal interval sums in sequences with bounded gaps (Erdős Problem 1213)

Erdős Problem 1213: for `a, K ≥ 1`, is there `f(a, K)` such that every integer sequence `a = a₁ < ⋯
< aₛ` with gaps at most `K` and `aₛ > f(a, K)` has two distinct intervals of indices with equal
sums?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

namespace MathlibExt.NumberTheory.BoundedGapEqualIntervalSumsErdosProblem1213Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #1213, https://www.erdosproblems.com/1213 (status
PROVED). UnsolvedMath record UM-30007254 (`EP-1213`), dataset ulamai/UnsolvedMath v1.8.0.

The sequence is `a 0, …, a (s - 1)` (indices shifted by one); intervals are nonempty ranges of
consecutive indices `[i, j]`. Compared with the formal-conjectures statement
`ErdosProblems/1213.lean` (equivalent; no code imported).
-/

/-- Among the terms `a 0, …, a (s - 1)`, two distinct intervals of consecutive indices
`[i, j] ≠ [i', j']` have equal sums. -/
def HasEqualIntervalSums (a : ℕ → ℕ) (s : ℕ) : Prop :=
  ∃ i j i' j' : ℕ, i ≤ j ∧ j < s ∧ i' ≤ j' ∧ j' < s ∧ (i, j) ≠ (i', j') ∧
    ∑ t ∈ Finset.Icc i j, a t = ∑ t ∈ Finset.Icc i' j', a t

/-- Erdős Problem 1213: for all `a₁, K ≥ 1` there is `f(a₁, K)` such that every strictly
increasing integer sequence `a₁ = a 0 < a 1 < ⋯ < a (s - 1)` with gaps at most `K` and last term
greater than `f(a₁, K)` has two distinct intervals with equal sums. -/
def boundedGapEqualIntervalSums : Prop :=
  ∀ a₁ K : ℕ, 1 ≤ a₁ → 1 ≤ K → ∃ f : ℕ, ∀ (s : ℕ) (a : ℕ → ℕ), 0 < s → a 0 = a₁ →
    (∀ t, t + 1 < s → a t < a (t + 1) ∧ a (t + 1) ≤ a t + K) → f < a (s - 1) →
      HasEqualIntervalSums a s

/--
Resolved true: Hegyvári proved the answer is yes, with `f(a, K) ≪ a e^{O(K)}`;
erdosproblems.com/1213 lists the problem as proved. Source: T. F. Bloom, Erdős Problems, Problem
#1213, https://www.erdosproblems.com/1213 (status PROVED); resolution: N. Hegyvári, On consecutive
sums in sequences, Acta Math. Hungar. 48 (1986), 193-200, erdosproblems.com/1213: proved by Hegyvári
with f(a, K) ≪ a e^{O(K)}, https://doi.org/10.1007/BF01949064.
-/
public theorem_wanted boundedGapEqualIntervalSums_holds : boundedGapEqualIntervalSums

end MathlibExt.NumberTheory.BoundedGapEqualIntervalSumsErdosProblem1213Wanted
