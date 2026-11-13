/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Sets whose subset sums of different sizes are disjoint (Erdős Problem 874)

Erdős Problem 874 (Erdős and Straus): let `k(N)` be the size of the largest `A ⊆ {1, …, N}` such
that the sets `S_r = {a_1 + ⋯ + a_r : a_1 < ⋯ < a_r ∈ A}` are disjoint for distinct `r ≥ 1`.
Estimate `k(N)`; in particular, is `k(N) ∼ 2 N^{1/2}`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Real.Sqrt

@[expose] public section

namespace MathlibExt.NumberTheory.DisjointSubsetSumLevelsErdosProblem874Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #874, https://www.erdosproblems.com/874 (status
PROVED). UnsolvedMath record UM-30007068 (`EP-874`), dataset ulamai/UnsolvedMath v1.8.0.

`S_r` uses `r` distinct elements, so the condition is that nonempty subsets of `A` of different
sizes have different sums. `k(N) ∼ 2 √N` is stated as: for every `ε > 0` and all large `N`, some
admissible `A ⊆ {1, …, N}` has at least `(2 - ε) √N` elements and none has more than `(2 + ε) √N`.
formal-conjectures has no statement of this problem.
-/

/-- The sets `S_r` of sums of `r` distinct elements of `A` are pairwise disjoint for distinct
`r ≥ 1`. -/
def HasDisjointSubsetSumLevels (A : Finset ℕ) : Prop :=
  ∀ S ⊆ A, ∀ T ⊆ A, S.Nonempty → T.Nonempty → S.card ≠ T.card → ∑ a ∈ S, a ≠ ∑ a ∈ T, a

/-- Erdős Problem 874 (Erdős and Straus): `k(N) ∼ 2 √N`, where `k(N)` is the largest size of such a
set in `{1, …, N}`. -/
def disjointSubsetSumLevelsAsymptotic : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in Filter.atTop,
    (∃ A ⊆ Finset.Icc 1 N, HasDisjointSubsetSumLevels A ∧ (2 - ε) * Real.sqrt N ≤ A.card) ∧
    ∀ A ⊆ Finset.Icc 1 N, HasDisjointSubsetSumLevels A → (A.card : ℝ) ≤ (2 + ε) * Real.sqrt N

/--
Resolved true: Deshouillers and Freiman proved `k(N) ∼ 2 N^{1/2}` for all large `N` (Straus had
shown `lim inf k(N) / N^{1/2} ≥ 2`); erdosproblems.com/874 lists the problem as proved. Source: T.
F. Bloom, Erdős Problems, Problem #874, https://www.erdosproblems.com/874 (status PROVED);
resolution: J.-M. Deshouillers and G. A. Freiman, On an additive problem of Erdős and Straus, 2,
Astérisque 258 (1999), 141-148, abstract: an admissible set in [1, N] (sums of s and of t pairwise
distinct elements disjoint for s ≠ t) has maximal cardinality when it consists of consecutive
integers at the upper end of [1, N], as Erdős conjectured, proved for N sufficiently large;
erdosproblems.com/874: Straus showed (N - k, N] admissible for k = 2m - 1 when N ∈ [m², m² + m) and
k = 2m when N ∈ [m² + m, (m + 1)²), and the conjecture k(N) ∼ 2N^{1/2} was proved (for all large N)
by Deshouillers and Freiman, https://doi.org/10.24033/ast.442.
-/
public theorem_wanted disjointSubsetSumLevelsAsymptotic_holds : disjointSubsetSumLevelsAsymptotic

end MathlibExt.NumberTheory.DisjointSubsetSumLevelsErdosProblem874Wanted
