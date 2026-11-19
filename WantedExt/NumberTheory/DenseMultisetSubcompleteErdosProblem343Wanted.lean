/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Dense multisets are subcomplete (Erdős Problem 343)

Erdős Problem 343 (a problem of Folkman): if `A ⊆ ℕ` is a multiset with `|A ∩ {1, …, N}| ≫ N` for
all `N`, must `A` be subcomplete, i.e. must `P(A) = {∑_{n ∈ B} n : B ⊆ A finite}` contain an
infinite arithmetic progression?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

namespace MathlibExt.NumberTheory.DenseMultisetSubcompleteErdosProblem343Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #343, https://www.erdosproblems.com/343 (status PROVED
(LEAN)); P. Erdős and R. L. Graham, Old and new problems and results in combinatorial number theory
(1980), p. 54. UnsolvedMath record UM-30006830 (`EP-343`), dataset ulamai/UnsolvedMath v1.8.0.

The multiset has `m n < ∞` copies of each positive integer `n`, and `|A ∩ [1, N]|` counts
multiplicity. `≫ N` is read as `≥ C N` for a suitable absolute constant `C` and all large `N`
(erdosproblems.com's definitions page: `≫` hides an absolute constant, and dependence on a parameter
would be shown by a subscript, so `C` does not depend on `A`), exactly as in Szemerédi and Vu's
Theorem 6.3 (Folkman's conjecture: there is a constant `C` such that every non-decreasing sequence
of positive integers with `A(n) ≥ C n` for all sufficiently large `n` is subcomplete, where `A(n)`
counts the terms in `[1, n]` with repetition); this is implied by the arbitrary-constant reading. No
formal-conjectures statement exists for 343.
-/

open Filter

/-- `P(A)` for the multiset `A` containing `m n` copies of each positive integer `n`: the sums
`∑_{n ∈ T} j n * n` over finite sets `T` of positive integers and `j n ≤ m n`. -/
def multisetSubsetSums (m : ℕ → ℕ) : Set ℕ :=
  {s | ∃ (T : Finset ℕ) (j : ℕ → ℕ), (∀ n ∈ T, 0 < n ∧ j n ≤ m n) ∧ s = ∑ n ∈ T, j n * n}

/-- Erdős Problem 343, with `|A ∩ {1, …, N}| ≫ N` read as `≥ C N` for a suitable absolute
constant `C`: every multiset of positive integers with at least `C N` elements in `[1, N]`
(counted with multiplicity) for all large `N` is subcomplete. -/
def denseMultisetSubcomplete : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ → ℕ, (∀ᶠ N : ℕ in atTop, C * N ≤ ∑ n ∈ Finset.Icc 1 N, (m n : ℝ)) →
    ∃ a d : ℕ, 0 < d ∧ ∀ i : ℕ, a + i * d ∈ multisetSubsetSums m

/--
Resolved true: Szemerédi and Vu proved Folkman's conjecture (their Theorem 6.3): for a suitable
absolute constant `C`, every multiset of positive integers with at least `C N` elements in `[1, N]`
(counted with multiplicity) for all large `N` is subcomplete. Folkman's examples with `≫ N^{1-ε}`
show the exponent cannot be lowered. erdosproblems.com/343 lists the problem as proved. Source: T.
F. Bloom, Erdős Problems, Problem #343, https://www.erdosproblems.com/343 (status PROVED (LEAN)); P.
Erdős and R. L. Graham, Old and new problems and results in combinatorial number theory (1980), p.
54; resolution: E. Szemerédi and V. Vu, Long arithmetic progressions in sumsets: thresholds and
bounds, J. Amer. Math. Soc. (2006), 119-169, arXiv:math/0507539, Theorem 6.3 (Folkman's Conjecture
6.1): there is a constant C such that every non-decreasing sequence a_1 ≤ a_2 ≤ ⋯ of positive
integers with A(n) ≥ Cn for all sufficiently large n, A(n) counting the terms between 1 and n, is
subcomplete; erdosproblems.com/343: the question was answered yes by Szemerédi and Vu; Folkman had
the case |A ∩ [1, N]| ≫ N^{1+ε} and a non-subcomplete multiset with ≫ N^{1-ε},
https://arxiv.org/abs/math/0507539.
-/
public theorem_wanted denseMultisetSubcomplete_holds : denseMultisetSubcomplete

end MathlibExt.NumberTheory.DenseMultisetSubcompleteErdosProblem343Wanted
