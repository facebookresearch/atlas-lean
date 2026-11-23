/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Subsets of `{1, …, N}` with no square subset sum (Erdős Problem 587)

Erdős Problem 587: what is the size of the largest `A ⊆ {1, …, N}` such that for every nonempty `S ⊆
A` the sum of the elements of `S` is not a square?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

namespace MathlibExt.NumberTheory.NoSquareSubsetSumErdosProblem587Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #587, https://www.erdosproblems.com/587 (status
SOLVED). UnsolvedMath record UM-30006943 (`EP-587`), dataset ulamai/UnsolvedMath v1.8.0.

The answer is formalized as the known order: at least `c N^{1/3}` (Erdős' construction) and at most
`N^{1/3} (log N)^C` for all large `N` (Nguyen and Vu), so the maximum is `N^{1/3 + o(1)}`; the exact
size is not known. Compared with the formal-conjectures file `ErdosProblems/587.lean`, which states
only the Nguyen-Vu upper bound as a variant (no code imported).
-/

/-- No nonempty subset of `A` sums to a perfect square (`A` is square-sum-free in the sense of
Nguyen and Vu). -/
def HasNoSquareSubsetSum (A : Finset ℕ) : Prop :=
  ∀ S ⊆ A, S.Nonempty → ¬ IsSquare (∑ n ∈ S, n)

/-- The largest size of a subset of `{1, …, N}` none of whose nonempty subsets sums to a square. -/
noncomputable def maxNoSquareSubsetSum (N : ℕ) : ℕ :=
  sSup {k | ∃ A ⊆ Finset.Icc 1 N, HasNoSquareSubsetSum A ∧ A.card = k}

/-- Erdős Problem 587, in the form of its solution: the largest subset of `{1, …, N}` with no
nonempty subset summing to a square has between `c N^{1/3}` and `N^{1/3} (log N)^C` elements for
all large `N`. -/
def maxNoSquareSubsetSumOrder : Prop :=
  ∃ c > (0 : ℝ), ∃ C : ℝ, ∀ᶠ N : ℕ in Filter.atTop,
    c * (N : ℝ) ^ (1 / 3 : ℝ) ≤ maxNoSquareSubsetSum N ∧
      (maxNoSquareSubsetSum N : ℝ) ≤ (N : ℝ) ^ (1 / 3 : ℝ) * Real.log N ^ C

/--
Resolved true: Erdős observed that `|A| ≫ N^{1/3}` is possible (the first `≈ N^{1/3}` multiples of a
prime `p ≈ N^{2/3}`), and Nguyen and Vu proved `|A| ≤ N^{1/3} (log N)^C` for large `N`;
erdosproblems.com/587 lists the problem as solved. Source: T. F. Bloom, Erdős Problems, Problem
#587, https://www.erdosproblems.com/587 (status SOLVED); resolution: H. H. Nguyen and V. H. Vu,
Squares in sumsets, in An Irregular Mind (2010), 491-524, arXiv:0811.1311, abstract: the maximum
cardinality is of order n^{1/3+o(1)}; inequality (7): SF(n) ≤ n^{1/3} (log n)^C; lower bound N^{1/3}
≪ |A| by Erdős' construction (erdosproblems.com/587, 'essentially solved'),
https://arxiv.org/abs/0811.1311.
-/
public theorem_wanted maxNoSquareSubsetSumOrder_holds : maxNoSquareSubsetSumOrder

end MathlibExt.NumberTheory.NoSquareSubsetSumErdosProblem587Wanted
