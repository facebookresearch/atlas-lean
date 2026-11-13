/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The squares are Ramsey `2`-complete (Erdős Problem 843)

Erdős Problem 843 (Burr and Erdős): are the squares Ramsey `2`-complete? That is, in any
`2`-coloring of the square numbers, can every sufficiently large `n ∈ ℕ` be written as a
monochromatic sum of distinct squares?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Order.Filter.AtTopBot.Defs

@[expose] public section

namespace MathlibExt.NumberTheory.SquaresRamseyCompleteErdosProblem843Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #843, https://www.erdosproblems.com/843 (status
PROVED). UnsolvedMath record UM-30007058 (`EP-843`), dataset ulamai/UnsolvedMath v1.8.0.

The coloring of the positive squares is given on their roots (`col m` is the color of `m²`); the
threshold may depend on the coloring and the color on `N` (Burr and Erdős's definition, as in
Conlon, Fox and Pham). formal-conjectures has no statement of this problem.
-/

/-- Erdős Problem 843 (Burr and Erdős): for every `2`-coloring of the positive squares (`col m` is
the color of `m²`), every large `N` is a sum of distinct squares of one color. -/
def squaresRamseyTwoComplete : Prop :=
  ∀ col : ℕ → Fin 2, ∀ᶠ N : ℕ in Filter.atTop, ∃ (i : Fin 2) (S : Finset ℕ),
    (∀ m ∈ S, 0 < m ∧ col m = i) ∧ ∑ m ∈ S, m ^ 2 = N

/--
Resolved true: Conlon, Fox and Pham proved that every complete polynomial sequence, in particular
the squares, contains an `r`-Ramsey complete subsequence for every `r ≥ 2` (Burr's announced proof
was never published); erdosproblems.com/843 lists the problem as proved. Source: T. F. Bloom, Erdős
Problems, Problem #843, https://www.erdosproblems.com/843 (status PROVED); resolution: D. Conlon, J.
Fox and H. T. Pham, Subset sums, completeness and colorings, arXiv:2104.14766 (2021), Theorem 1.2:
for every polynomial P of degree k with (P(m))_{m ≥ 1} complete and every r ≥ 2 there is an r-Ramsey
complete subsequence of (P(m))_{m ≥ 1}; erdosproblems.com/843: a stronger version was proved by
Conlon, Fox and Pham (Burr's proof was never published), https://arxiv.org/abs/2104.14766.
-/
public theorem_wanted squaresRamseyTwoComplete_holds : squaresRamseyTwoComplete

end MathlibExt.NumberTheory.SquaresRamseyCompleteErdosProblem843Wanted
