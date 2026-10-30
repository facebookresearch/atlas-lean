/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# An improved upper bound for Sidon subsets of [N] (Green's Problem 31)

B. Green, 100 open problems, Problem 31: write `F(N)` for the largest Sidon subset of `[N]`.
Improve, at least for infinitely many `N`, the bounds `N^{1/2} + O(1) ≤ F(N) ≤ N^{1/2} + N^{1/4} +
O(1)`.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import MathlibExt.Combinatorics.Additive.Sidon

@[expose] public section

namespace MathlibExt.Combinatorics.SidonUpperBoundImprovementGreenProblem31Wanted

/-!
Source: B. Green, 100 open problems, Problem 31 (manuscript, update of December 2025),
https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf. UnsolvedMath record UM-00000162
(`GREEN-074`), dataset ulamai/UnsolvedMath v1.8.0.

`F(N)` is the largest size of a Sidon subset of `{1, …, N}` (MathlibExt `Set.IsSidon`: all pairwise
sums distinct up to order). The target is the improvement of Lindström's upper bound recorded in
Green's own update to Problem 31: `F(N) ≤ N^{1/2} + c N^{1/4}` for all large `N` with a constant `c
< 1`. The open-ended part of the problem (further improvements, and any improvement of the lower
bound) is not formalized.
-/

/-- `F(N)`: the largest size of a Sidon subset of `[N] = {1, …, N}`. -/
noncomputable def maxSidonSubsetSize (N : ℕ) : ℕ :=
  sSup {k | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ (A : Set ℕ).IsSidon ∧ A.card = k}

/-- Green's Problem 31, upper bound: Lindström's bound `F(N) ≤ N^{1/2} + N^{1/4} + O(1)` can be
improved, in the form `F(N) ≤ N^{1/2} + c N^{1/4}` for all large `N` with a constant `c < 1`. -/
def sidonUpperBoundImproved : Prop :=
  ∃ c : ℝ, c < 1 ∧ ∃ N₀ : ℕ, ∀ N, N₀ ≤ N →
    (maxSidonSubsetSize N : ℝ) ≤ Real.sqrt N + c * (N : ℝ) ^ ((1 : ℝ) / 4)

/--
Resolved true: Balogh, Füredi and Roy proved `F(N) ≤ N^{1/2} + 0.998 N^{1/4}` for all large `N`,
improving Lindström's bound as Green's update to Problem 31 records (Carter, Hunter and O'Bryant
later lowered the constant to `0.98183`). Source: B. Green, 100 open problems, Problem 31
(manuscript, update of December 2025),
https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf; resolution: J. Balogh, Z. Füredi and
S. Roy, An upper bound on the size of Sidon sets, Amer. Math. Monthly 130 (2023), 437-445,
doi:10.1080/00029890.2023.2176667; arXiv:2103.15850, abstract: the maximum size of a Sidon set of
{1, ..., n} is at most √n + 0.998 n^{1/4} for sufficiently large n; Green, Problem 31, 'Update 2021'
records this bound and its 2023 improvement to 0.98183 (D. Carter, Z. Hunter and K. O'Bryant, Acta
Math. Hungar. 175 (2025), 108-126), https://doi.org/10.1080/00029890.2023.2176667.
-/
public theorem_wanted sidonUpperBoundImproved_holds : sidonUpperBoundImproved

end MathlibExt.Combinatorics.SidonUpperBoundImprovementGreenProblem31Wanted
