/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The Erdős-Fuchs theorem (Erdős Problem 763)

Erdős Problem 763 (Erdős and Turán): let `A ⊆ ℕ`. Can there exist a constant `c > 0` such that `∑_{n
≤ N} 1_A ∗ 1_A (n) = c N + O(1)`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
public import MathlibExt.Combinatorics.Additive.RepresentationCount

@[expose] public section

namespace MathlibExt.NumberTheory.ErdosFuchsPairRepresentationsErdosProblem763Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #763, https://www.erdosproblems.com/763 (status
DISPROVED). UnsolvedMath record UM-30007021 (`EP-763`), dataset ulamai/UnsolvedMath v1.8.0.

`1_A ∗ 1_A (n)` is the convolution, the number of ordered pairs `(a, b) ∈ A × A` with `a + b = n`,
`MathlibExt`'s `AdditiveCombinatorics.orderedRepresentationCount`; `A` may contain `0`. `c N + O(1)`
is a uniform bound `|∑_{n ≤ N} 1_A ∗ 1_A (n) - c N| ≤ C` for all `N` (equivalent to an eventual
bound, the sum being finite for each `N`). Compared with the formal-conjectures statement
`ErdosProblems/763.lean` (equivalent; no code imported).
-/

/-- Erdős Problem 763 (Erdős and Turán): some `A ⊆ ℕ` and `c > 0` satisfy
`∑_{n ≤ N} 1_A ∗ 1_A (n) = c N + O(1)`, where `1_A ∗ 1_A (n)` is
`AdditiveCombinatorics.orderedRepresentationCount A n`, the number of ordered pairs of elements of
`A` with sum `n`. -/
def pairRepresentationSumLinear : Prop :=
  ∃ (A : Set ℕ) (c : ℝ), 0 < c ∧ ∃ C : ℝ, ∀ N : ℕ,
    |(∑ n ∈ Finset.range (N + 1),
      (AdditiveCombinatorics.orderedRepresentationCount A n : ℝ)) - c * N| ≤ C

/--
Resolved false: Erdős and Fuchs proved that `∑_{n ≤ N} 1_A ∗ 1_A (n) = c N + o(N^{1/4} (log
N)^{-1/2})` is impossible for every `A ⊆ ℕ` and `c > 0`, so in particular the error cannot be
`O(1)`; erdosproblems.com/763 lists the problem as disproved. Source: T. F. Bloom, Erdős Problems,
Problem #763, https://www.erdosproblems.com/763 (status DISPROVED); resolution: P. Erdős and W. H.
J. Fuchs, On a problem of additive number theory, J. London Math. Soc. 31 (1956), 67-73, Theorem 1:
for an infinite sequence 0 ≤ a_1 < a_2 < ⋯ and r(n) the number of solutions of a_i + a_j ≤ n, r(n) =
cn + o(n^{1/4} (log n)^{-1/2}) cannot hold if c > 0, and 'our theorem is true for every one of the
three interpretations', interpretation (I) counting ordered pairs (generating function g(z)²),
https://users.renyi.hu/~p_erdos/1956-07.pdf.
-/
public theorem_wanted pairRepresentationSumLinear_refuted : ¬ pairRepresentationSumLinear

end MathlibExt.NumberTheory.ErdosFuchsPairRepresentationsErdosProblem763Wanted
