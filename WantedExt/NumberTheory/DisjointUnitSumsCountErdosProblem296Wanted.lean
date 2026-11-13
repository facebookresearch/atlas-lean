/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Disjoint unit-sum subsets of `{1, …, N}` (Erdős Problem 296)

Erdős Problem 296: let `k(N)` be the largest `k` such that there are disjoint `A₁, …, A_k ⊆ {1, …,
N}` with `∑_{n ∈ A_i} 1/n = 1` for all `i`. Estimate `k(N)`. Is `k(N) = o(log N)`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

namespace MathlibExt.NumberTheory.DisjointUnitSumsCountErdosProblem296Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #296, https://www.erdosproblems.com/296 (status PROVED
(LEAN)); P. Erdős and R. L. Graham, Old and new problems and results in combinatorial number theory
(1980). UnsolvedMath record UM-30006811 (`EP-296`), dataset ulamai/UnsolvedMath v1.8.0.

Two targets: the estimate `k(N) = (1 + o(1)) log N` and the question `k(N) = o(log N)` (answered
no). `k(N)` is a maximum, as `k(N) ≤ ∑_{n ≤ N} 1/n`. Compared with the formal-conjectures statement
`ErdosProblems/296.lean` (equivalent to the estimate, stated there as two bounds; no code imported).
-/

open Filter Topology Asymptotics

/-- There are `k` pairwise disjoint subsets of `{1, …, N}`, each with reciprocal sum `1`. -/
def HasDisjointUnitSums (N k : ℕ) : Prop :=
  ∃ A : Fin k → Finset ℕ, (∀ i, A i ⊆ Finset.Icc 1 N) ∧ (∀ i, ∑ n ∈ A i, (1 : ℚ) / n = 1) ∧
    Pairwise fun i j => Disjoint (A i) (A j)

/-- `k(N)`: the largest such `k` (at most `∑_{n ≤ N} 1/n`). -/
noncomputable def maxDisjointUnitSums (N : ℕ) : ℕ :=
  sSup {k | HasDisjointUnitSums N k}

/-- Erdős Problem 296, estimate: `k(N) = (1 + o(1)) log N`. -/
def maxDisjointUnitSumsAsymptotic : Prop :=
  Tendsto (fun N : ℕ => (maxDisjointUnitSums N : ℝ) / Real.log N) atTop (𝓝 1)

/-- Erdős Problem 296, question: `k(N) = o(log N)`. -/
def maxDisjointUnitSumsLittleO : Prop :=
  (fun N : ℕ => (maxDisjointUnitSums N : ℝ)) =o[atTop] fun N : ℕ => Real.log N

/--
Resolved true: disjointness gives `k(N) ≤ ∑_{n ≤ N} 1/n = log N + O(1)`, and Hunter and Sawhney
observed that Bloom's Theorem 3, applied greedily to the unused integers, gives `k(N) = (1 - o(1))
log N`. erdosproblems.com/296 lists the problem as proved. Source: T. F. Bloom, Erdős Problems,
Problem #296, https://www.erdosproblems.com/296 (status PROVED (LEAN)); P. Erdős and R. L. Graham,
Old and new problems and results in combinatorial number theory (1980); resolution: T. F. Bloom, On
a density conjecture about unit fractions, arXiv:2112.03726 (2021); formalized in Lean 3 by T. F.
Bloom and B. Mehta (github.com/b-mehta/unit-fractions), erdosproblems.com/296: Hunter and Sawhney
observed that Theorem 3 of [Bl21] (A ⊆ [1, N] with ∑_{n∈A} 1/n ≥ C (log log log N / log log N) log N
contains S with ∑_{n∈S} 1/n = 1), with the greedy argument, gives k(N) = (1 - o(1)) log N; k(N) ≤
∑_{n ≤ N} 1/n is trivial, https://www.erdosproblems.com/296.
-/
public theorem_wanted maxDisjointUnitSumsAsymptotic_holds : maxDisjointUnitSumsAsymptotic

/--
Resolved false: `k(N) = (1 - o(1)) log N` (Hunter and Sawhney, from Bloom's Theorem 3 and the greedy
argument), so `k(N)` is not `o(log N)`. erdosproblems.com/296 lists the problem as proved. Source:
T. F. Bloom, Erdős Problems, Problem #296, https://www.erdosproblems.com/296 (status PROVED (LEAN));
P. Erdős and R. L. Graham, Old and new problems and results in combinatorial number theory (1980);
resolution: T. F. Bloom, On a density conjecture about unit fractions, arXiv:2112.03726 (2021);
formalized in Lean 3 by T. F. Bloom and B. Mehta (github.com/b-mehta/unit-fractions),
erdosproblems.com/296: Hunter and Sawhney observed that Theorem 3 of [Bl21] (A ⊆ [1, N] with ∑_{n∈A}
1/n ≥ C (log log log N / log log N) log N contains S with ∑_{n∈S} 1/n = 1), with the greedy
argument, gives k(N) = (1 - o(1)) log N; k(N) ≤ ∑_{n ≤ N} 1/n is trivial,
https://www.erdosproblems.com/296.
-/
public theorem_wanted maxDisjointUnitSumsLittleO_refuted : ¬ maxDisjointUnitSumsLittleO

end MathlibExt.NumberTheory.DisjointUnitSumsCountErdosProblem296Wanted
