/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Largest non-averaging sets (Erdős Problem 186)

Erdős Problem 186: let `F(N)` be the largest size of a non-averaging `A ⊆ {1, …, N}`, one in which
no element is the arithmetic mean of at least two elements of `A`. What is the order of growth of
`F(N)`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

namespace MathlibExt.Combinatorics.NonAveragingSetSizeErdosProblem186Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #186, https://www.erdosproblems.com/186 (status
SOLVED). UnsolvedMath record UM-30006755 (`EP-186`), dataset ulamai/UnsolvedMath v1.8.0.

Following Pham and Zakharov, `A` is non-averaging when no `a ∈ A` is the mean of a nonempty `S ⊆ A \
{a}`. For sets of distinct elements this is the source's "mean of at least two elements of `A`": a
singleton `S` has mean `s ≠ a`, and adding `a` to `S` does not change whether the mean is `a`. The
answer `F(N) = N^{1/4 + o(1)}` is stated as `N^{1/4 - ε} ≤ F(N) ≤ N^{1/4 + ε}` for every `ε > 0` and
all large `N`. Compared with the formal-conjectures statement `ErdosProblems/186.lean` (`log F(N) /
log N → 1/4`, equivalent; no code imported).
-/

open Filter

/-- `A` is non-averaging: no `a ∈ A` is the arithmetic mean of a nonempty set `S ⊆ A \ {a}`
(equivalently, of at least two distinct elements of `A`). -/
def IsNonAveraging (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ S ⊆ A.erase a, S.Nonempty → ∑ s ∈ S, s ≠ S.card * a

/-- Erdős Problem 186: the largest non-averaging subset of `{1, …, N}` has size `N^{1/4 + o(1)}`:
for every `ε > 0` and all large `N` its size lies between `N^{1/4 - ε}` and `N^{1/4 + ε}`. -/
def nonAveragingMaxSizeQuarterExponent : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
    (∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ IsNonAveraging A ∧
      (N : ℝ) ^ ((1 : ℝ) / 4 - ε) ≤ A.card) ∧
    ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 N → IsNonAveraging A →
      (A.card : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 4 + ε)

/--
Resolved true: Bosznay constructed non-averaging subsets of `{1, …, N}` of size `≫ N^{1/4}`, and
Pham and Zakharov proved the matching upper bound `N^{1/4 + o(1)}`, so `F(N) = N^{1/4 + o(1)}`.
Source: T. F. Bloom, Erdős Problems, Problem #186, https://www.erdosproblems.com/186 (status
SOLVED); resolution: H. T. Pham and D. Zakharov, Sharp bound for the Erdős-Straus non-averaging set
problem, Geom. Funct. Anal. 35 (2025), 1712-1738, arXiv:2410.14624 (upper bound); Á. P. Bosznay, On
the lower estimation of non-averaging sets, Acta Math. Hungar. 53 (1989), 155-157 (lower bound),
Pham-Zakharov main theorem: the largest non-averaging subset of {1, …, n} has size n^{1/4 + o(1)};
erdosproblems.com/186: N^{1/4} ≪ F(N) ≪ N^{1/4 + o(1)}, https://arxiv.org/abs/2410.14624.
-/
public theorem_wanted nonAveragingMaxSizeQuarterExponent_holds : nonAveragingMaxSizeQuarterExponent

end MathlibExt.Combinatorics.NonAveragingSetSizeErdosProblem186Wanted
