/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Averages of new-denominator fraction counts (Erdős Problem 1000)

Erdős Problem 1000: for an increasing sequence `A = {n₁ < n₂ < ⋯}` let `φ_A(k)` count the `1 ≤ m ≤
n_k` for which `m / n_k` does not reduce to a fraction with an earlier denominator `n_j`. Is there a
sequence `A` with `(1 / N) ∑_{k ≤ N} φ_A(k) / n_k → 0`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

@[expose] public section

namespace MathlibExt.NumberTheory.NewDenominatorFractionsAverageErdosProblem1000Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #1000, https://www.erdosproblems.com/1000 (status
PROVED (LEAN)). UnsolvedMath record UM-30007118 (`EP-1000`), dataset ulamai/UnsolvedMath v1.8.0.

The sequence is `n 0 < n 1 < ⋯` with `n 0 > 0`. `φ_A(k)` is Cassels' function, the one Haight's
result is about; Erdős (Problems and results on diophantine approximations, Compositio Math. 16
(1964), 52-65, the definition before (20)) defines it as the number of `1 ≤ a ≤ n_k` with
`a / n_k ≠ b / n_j` for every integer `b` and every `1 ≤ j < k`. So `m` is counted when `m / n_k`
cannot be written with denominator `n_j` for any `j < k`, i.e. its reduced denominator
`n_k / (m, n_k)` divides no earlier `n_j`. Partial scope relative to the page's literal wording: its
parenthetical `n_k / (m, n_k) ≠ n_j` excludes fewer `m`, so it gives larger counts and a stronger
claim, which is not what Haight resolved and is not formalized; only Cassels' original formulation
is. Compared with the formal-conjectures statement `ErdosProblems/1000.lean` (identical definition
and target; no code imported).
-/

/-- `φ_A(k)` for a sequence `n₀ < n₁ < ⋯` of positive integers: the number of `1 ≤ m ≤ n_k` such
that `m / n_k` cannot be written as a fraction with denominator `n_j` for any `j < k`, that is, its
reduced denominator `n_k / gcd(m, n_k)` divides no earlier `n_j`. -/
def newFractionCount (n : ℕ → ℕ) (k : ℕ) : ℕ :=
  ((Finset.Icc 1 (n k)).filter fun m => ∀ j < k, ¬ (n k / Nat.gcd m (n k)) ∣ n j).card

/-- The average `(1 / N) ∑_{k < N} φ_A(k) / n_k` of the first `N` terms. -/
noncomputable def newFractionAverage (n : ℕ → ℕ) (N : ℕ) : ℝ :=
  (∑ k ∈ Finset.range N, (newFractionCount n k : ℝ) / n k) / N

/-- Erdős Problem 1000: some strictly increasing sequence of positive integers `n₀ < n₁ < ⋯` has
`(1 / N) ∑_{k < N} φ_A(k) / n_k → 0`. -/
def newFractionAverageTendsToZero : Prop :=
  ∃ n : ℕ → ℕ, StrictMono n ∧ 0 < n 0 ∧
    Filter.Tendsto (newFractionAverage n) Filter.atTop (nhds 0)

/--
Resolved true: Haight proved that some sequence has `(1 / N) ∑_{k ≤ N} φ_A(k) / n_k → 0`, contrary
to Erdős' expectation; erdosproblems.com/1000 lists the problem as proved, with a formal proof of
this statement in plby/lean-proofs (`Erdos1000.lean`). Source: T. F. Bloom, Erdős Problems, Problem
#1000, https://www.erdosproblems.com/1000 (status PROVED (LEAN)); resolution: J. A. Haight, Metric
Diophantine approximation and related topics, PhD thesis; formal proof plby/lean-proofs,
src/v4.29.1/ErdosProblems/Erdos1000.lean, erdosproblems.com/1000: Haight proved that such a sequence
exists (contrary to Erdős' expectation),
https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos1000.lean.
-/
public theorem_wanted newFractionAverageTendsToZero_holds : newFractionAverageTendsToZero

end MathlibExt.NumberTheory.NewDenominatorFractionsAverageErdosProblem1000Wanted
