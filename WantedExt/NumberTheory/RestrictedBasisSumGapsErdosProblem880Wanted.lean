/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Gaps between sums of distinct elements of a basis (Erdős Problem 880)

Erdős Problem 880 (Burr and Erdős): let `A ⊂ ℕ` be an additive basis of order `k` and let `B = {b_1
< b_2 < ⋯}` be the set of integers that are sums of `k` or fewer distinct elements of `A`. Is it
true that `b_{n+1} - b_n = O(1)` (the constant depending on `A` and `k`)?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import MathlibExt.Combinatorics.Additive.Basis
public import WantedExt.Combinatorics.SumsetPartitionErdosProblem741Wanted

@[expose] public section

namespace MathlibExt.NumberTheory.RestrictedBasisSumGapsErdosProblem880Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #880, https://www.erdosproblems.com/880 (status
PROVED). UnsolvedMath record UM-30007070 (`EP-880`), dataset ulamai/UnsolvedMath v1.8.0.

'Additive basis of order `k`' is Erdős's notion as quoted by Hegyvári, Hennecart and Plagne ('every
large integer is the sum of `k` or fewer of the `a`'s', repetitions allowed): `k (A ∪ {0})` contains
all large integers, `MathlibExt`'s `Set.IsAsymptoticAddBasisOfOrder` applied to `insert 0 A`; their
Theorem 1(ii) is stated in this form. Bounded gaps (`b_{n+1} - b_n = O(1)`) is `HasBoundedGaps` of
the Erdős Problem 741 entry, reused here: some `g` with every interval `[n, n + g)` meeting the set.
The answer depends on `k`: yes for `k = 2` (all large odd numbers lie in `B`, the trivial argument
on the page) and no for every `k ≥ 3`; only the `k ≥ 3` answer is stated. formal-conjectures has no
statement of this problem.
-/

open MathlibExt.Combinatorics.SumsetPartitionErdosProblem741Wanted (HasBoundedGaps)

/-- The integers that are sums of at most `k` distinct elements of `A`. -/
def restrictedSums (A : Set ℕ) (k : ℕ) : Set ℕ :=
  {N | ∃ S : Finset ℕ, S.card ≤ k ∧ (S : Set ℕ) ⊆ A ∧ ∑ a ∈ S, a = N}

/-- Erdős Problem 880 (Burr and Erdős) for some order `k ≥ 3`: for every `A ⊆ ℕ` such that every
large integer is a sum of at most `k` elements of `A` (`k (A ∪ {0})` contains all large integers,
`Set.IsAsymptoticAddBasisOfOrder`), the sums of at most `k` distinct elements of `A` have bounded
gaps. -/
def restrictedSumsBoundedGapsHighOrder : Prop :=
  ∃ k : ℕ, 3 ≤ k ∧ ∀ A : Set ℕ, (insert 0 A).IsAsymptoticAddBasisOfOrder k →
    HasBoundedGaps (restrictedSums A k)

/-- Deprecated: this entry's earlier local bounded-gaps predicate, kept with its original body.
The statement above now uses Erdős Problem 741's `HasBoundedGaps`, which is equivalent to it on
every set (`C ↦ C + 1`). -/
@[deprecated "Use `SumsetPartitionErdosProblem741Wanted.HasBoundedGaps` instead."
  (since := "2026-10-23")]
def HasBoundedGaps (B : Set ℕ) : Prop :=
  ∃ C : ℕ, ∀ x : ℕ, ∃ b ∈ B, x ≤ b ∧ b ≤ x + C

/--
Resolved false: Hegyvári, Hennecart and Plagne proved that for every `h ≥ 3` some `A` such that
every large integer is a sum of at most `h` elements of `A` has sums of at most `h` distinct
elements with unbounded gaps (Theorem 1(ii)), while for `h = 2` the gaps are eventually at most `2`
(Theorem 1(i)); erdosproblems.com/880 records the answer no for `k ≥ 3`. Source: T. F. Bloom, Erdős
Problems, Problem #880, https://www.erdosproblems.com/880 (status PROVED); resolution: N. Hegyvári,
F. Hennecart and A. Plagne, Answer to a question by Burr and Erdős on restricted addition, and
related results, Combin. Probab. Comput. 16 (2007), 747-756, Theorem 1(ii): for every h ≥ 3 there is
a set A with h({0} ∪ A) ∼ ℕ such that A ∪ 2 × A ∪ ⋯ ∪ h × A, the sums of at most h pairwise distinct
elements, has lim sup of consecutive gaps Δ = +∞; Theorem 1(i): if A ∪ 2A ∼ ℕ then Δ(A ∪ 2 × A) ≤ 2,
https://www.cmls.polytechnique.fr/perso/plagne/Erdos-Burr.pdf.
-/
public theorem_wanted restrictedSumsBoundedGapsHighOrder_refuted :
    ¬ restrictedSumsBoundedGapsHighOrder

end MathlibExt.NumberTheory.RestrictedBasisSumGapsErdosProblem880Wanted
